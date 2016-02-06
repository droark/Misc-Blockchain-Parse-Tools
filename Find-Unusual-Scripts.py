# (c) 2016 Douglas Roark
# Licensed under the MIT License. See LICENSE for the details.

from __future__ import print_function, division # Valid as of 2.6
import sys
sys.path.insert(0, '/home/droark/Projects/etotheipi-BitcoinArmory')
import binascii, hashlib, string, os
from collections import namedtuple
from math import ceil, log
from copy import deepcopy
# from armoryengine.BinaryPacker import * # Armory
from armoryengine.BinaryUnpacker import * # Armory
from armoryengine.ArmoryUtils import * # Armory

preBufZero = '\x00' * 4

# Quick-and-dirty enum.
class TxType:
    p2pKey    = 1
    p2pHash   = 2
    p2sh      = 3
    multiSig  = 4
    opReturn  = 5
    unknownTx = 6

# Transaction opcodes. Include only the ones we care about.
OP_0             = '\x00'
OP_1             = '\x51'
OP_2             = '\x52'
OP_3             = '\x53'
OP_RETURN        = '\x6a'
OP_DUP           = '\x76'
OP_EQUAL         = '\x87'
OP_EQUALVERIFY   = '\x88'
OP_HASH160       = '\xa9'
OP_CHECKSIG      = '\xac'
OP_CHECKMULTISIG = '\xae'

# OP_CHECKSIG hashtype values (https://en.bitcoin.it/wiki/OP_CHECKSIG)
NULL_BYTE            = '\x00' # A few sig/pubKey combos use a null byte.
SIGHASH_ALL          = '\x01'
SIGHASH_NONE         = '\x02'
SIGHASH_SINGLE       = '\x03'
SIGHASH_ANYONECANPAY = '\x80'

# ASN.1 encoding bytes
ASN1_INTEGER  = '\x02'
ASN1_SEQUENCE = '\x30'

# A global variable 'cause I'm being a lazy bastard. :) Used when printing data
# about a weird transaction. Useful for blockchain.info, blockexplorer.com, etc.
curTxHash = '\x00'

# Get a block file name based on a given number (blkXXXXX.dat).
# Input: A number between 0-99,999.
# Output: Block file name based on the input (e.g., blk00008.dat).
def getBCBlkFilename(fileNum):
    '''Create a Bitcoin block data file name based on the incoming number.'''
    if(fileNum < 0 or fileNum > 99999):
        print("Bad blkXXXXX.dat input number. Defaulting to blk99999.dat.")
        fileNum = 99999
    blkFile = os.path.join(BLKFILE_DIR, 'blk%05d.dat' % fileNum)
    return blkFile


# Read block header values and get the block header 2xSHA256 hash. The block
# header values are as follows, in the given order, and also returned in the
# same order. (The block header hash is returned last.)
# 1)Block header version  (4 bytes - Little endian)
# 2)Previous block header's hash  (32 bytes - Big endian)
# 3)Block transactions' merkle root  (32 bytes - Big endian)
# 4)Block timestamp  (4 bytes - Little endian)
# 5)Block difficulty "bits"  (4 bytes - Little endian)
# 6)Block nonce  (4 bytes - Little endian)
# Input: Raw data pointing to a block header.
# Output: The individual block header pieces, and the block header hash.
def getBlkHdrValues(header):
    '''Get the block header values & hash. Will read the data itself.'''
    # Get the block hash (endian-flipped result of 2xSHA256 block header
    # hash), then get the individual block pieces and return everything.
    blkHdrData = header.read(80)
    blkHdrHash = hash256(blkHdrData) # BE
    blkHdrUnpack = BinaryUnpacker(blkHdrData)
    blkVer = blkHdrUnpack.get(UINT32) # LE
    prevBlkHash = blkHdrUnpack.get(BINARY_CHUNK, 32) # BE
    blkMerkleRoot = blkHdrUnpack.get(BINARY_CHUNK, 32) # BE
    blkTimestamp = blkHdrUnpack.get(UINT32) # LE
    blkBits = blkHdrUnpack.get(UINT32) # LE
    blkNonce = blkHdrUnpack.get(UINT32) # LE
    return (blkVer, prevBlkHash, blkMerkleRoot, blkTimestamp, blkBits, \
            blkNonce, blkHdrHash)


# Look in a BinaryUnpacker object with a transaction input item and gets the
# pieces. The transaction input includes, in the following order:
# 1)A 2xSHA256 hash of a transaction being used as an input. (32 bytes - BE)
# 2)The index of the referenced output in the referenced trans.  (4 bytes - LE)
# 3)Transaction input's script length.  (VAR_INT - Little endian)
# 4)Transaction input's script.  (VAR_LEN - Big endian)
# 5)Sequence # (usually 0xFFFFFFFF, usually irrelevant).  (4 bytes - LE)
# Input: A BinaryUnpacker object with the transaction input.
# Output: The Tx input's individual objects and the TxIn binary string.
def getTxIn(txUnpack):
    '''Function that unpacks the items inside a transaction input.'''
    txStartPos = txUnpack.getPosition()

    # Get the individual Tx pieces.
    txInPrevHash = txUnpack.get(BINARY_CHUNK, 32) # BE
    txInPrevTxOutHashIdx = txUnpack.get(UINT32)
    txInScrLen = txUnpack.get(VAR_INT)
    txInScr = txUnpack.get(BINARY_CHUNK, txInScrLen)
    txInSeqNum = txUnpack.get(UINT32)

    # While we're here, let's get the Tx binary string itself.
    txLen = txUnpack.getPosition() - txStartPos
    txUnpack.rewind(txLen)
    txInStr = txUnpack.get(BINARY_CHUNK, txLen)

    return (txInPrevHash, txInPrevTxOutHashIdx, txInScrLen, txInScr, \
            txInSeqNum, txInStr)


# Look in a BinaryUnpacker object with a transaction output item and gets the
# pieces. The transaction output includes, in the following order:
# 1)The amount sent in the transaction.  (8 bytes - LE)
# 2)Transaction output's script length.  (VAR_INT - LE)
# 3)Transaction output's script.  (VAR_LEN - BE)
# Input: A BinaryUnpacker object with the transaction input.
# Output: The Tx output's individual objects and the TxOut binary string.
def getTxOut(txUnpack):
    '''Function that unpacks the items inside a transaction output.'''
    txStartPos = txUnpack.getPosition()

    # Get the individual Tx pieces.
    txOutVal = txUnpack.get(UINT64)
    txOutScrLen = txUnpack.get(VAR_INT)
    txOutScr = txUnpack.get(BINARY_CHUNK, txOutScrLen)

    # While we're here, let's get the Tx binary string itself.
    txLen = txUnpack.getPosition() - txStartPos
    txUnpack.rewind(txLen)
    txOutStr = txUnpack.get(BINARY_CHUNK, txLen)

    return (txOutVal, txOutScrLen, txOutScr, txOutStr)


# Look in a BinaryUnpacker object with a transaction item and gets the pieces.
# The transaction includes, in the following order:
# 1)Transaction version number. (4 bytes - Little endian)
# 2)Number of transaction inputs. (VAR INT - LE)
# 3)Transaction inputs. (VAR_LEN - Big endian)
# 4)Number of transaction outputs. (VAR INT - LE)
# 5)Transaction outputs. (VAR_LEN - BE)
# 6)Transaction lock time. (4 bytes - LE)
# Input: A BinaryUnpacker object with the transaction.
# Output: The transaction's individual objects, and the 2xSHA256 hash of the
# transaction. The inputs & outputs will be returned in lists.
def getTxObj(txUnpack):
    '''Function that unpacks the items inside a transaction.'''
    txInList = []
    txOutList = []
    txInStr = b''
    txOutStr = b''
    unpackStartPos = txUnpack.getPosition()

    # Get the Tx version and the inputs. Put the inputs in a list.
    txVer = txUnpack.get(UINT32) # Item 1
    numTxIn = txUnpack.get(VAR_INT) # Item 2
    txInCtr = numTxIn
    while(txInCtr > 0):
        txInPrevHash, txInPrevTxOutHashIdx, txInScrLen, txInScr, txInSeqNum, \
        txInStr = getTxIn(txUnpack) # Item 3
        txInList.append(txInStr)
        txInCtr -= 1

    # Get the Tx outputs and put them in a list.
    numTxOut = txUnpack.get(VAR_INT) # Item 4
    txOutCtr = numTxOut
    while(txOutCtr > 0):
        txOutVal, txOutScrLen, txOutScr, txOutStr = getTxOut(txUnpack) # Item 5
        txOutList.append(txOutStr)
        txOutCtr -= 1

    # Get the Tx lock time.
    txLockTime = txUnpack.get(UINT32) # Item 6

    # Because the reference Bitcoin client currently tolerates non-canonical
    # VAR_INT objects, we're not allowed to recreate a hash from the individual
    # Tx elements. It's a possible Tx malleability attack. Once the client
    # disallows non-canonical VAR_INTs, we can hash the pieces. 'Til then, we
    # must rewind and hash the entire Tx.
    txLen = txUnpack.getPosition() - unpackStartPos
    txUnpack.rewind(txLen)
    txStr = txUnpack.get(BINARY_CHUNK, txLen)
    txHash = hash256(txStr)

    return (txVer, numTxIn, txInList, numTxOut, txOutList, txLockTime, txHash)


# Function that determines if a BinaryUnpacker object contains an ECDSA public
# key, as defined by X9.62. The function only determines if the format is
# correct, not if the key is actually valid. The format is:
#   Compressed key - (0x02 or 0x03) + 32 bytes
#   Uncompressed key - 0x04 + 64 bytes
# Input: BinaryUnpacker object pointing to a supposed ECDSA public key. The
#        object will be rewound to its starting position at the end.
# Output: 0 if the key is invalid, or the key length if the key is valid.
def isPubKey(pkIn):
    '''Determine if a chunk of data is an ECDSA public key (X9.62 encoding).'''
    retVal = 0
    rewindVal = 0   # Here only so that future changes are made obvious.

    # There must be at least 33 bytes left to read.
    if(pkIn.getRemainingSize() >= 33):
        initByte = pkIn.get(BINARY_CHUNK, 1)
        rewindVal += 1
        if(initByte == '\x02' or initByte == '\x03'): # Compressed key
            retVal = 33
        elif(initByte == '\x04'):                     # Uncompressed key
            # The previous length check wasn't adequate for uncompressed keys.
            # Make sure there's enough data before confirming the key is valid.
            if(pkIn.getRemainingSize() >= 64):
                retVal = 65

    # Rewind and return.
    pkIn.rewind(rewindVal)
    return retVal


# Function that determines if a hash byte is a valid SIGHASH byte. We'll also
# accept NULL (i.e., 0x00) byte. See https://en.bitcoin.it/wiki/OP_CHECKSIG for
# more details.
# Input:  A byte to check.
# Output: True if a byte's valid, False if not.
def isValidSigHashByte(inByte):
    '''Determine if a byte is a valid SIGHASH byte.'''
    retVal = False
    
    # HACK ALERT: Some scriptSig objects have a NULL byte present instead of a
    # proper SIGHASH byte. We'll accept it.
    if(inByte == NULL_BYTE or inByte == SIGHASH_ALL or inByte == SIGHASH_NONE or
       inByte == SIGHASH_SINGLE or inByte == SIGHASH_ANYONECANPAY):
        retVal = True
    return retVal


# Function that determines if a BinaryUnpacker object contains an ECDSA
# signature or signatures, as defined by X9.62, plus a byte used by OP_CHECKSIG
# to determine how the Tx will be hashed. The function only determines if the
# format is correct, not if the signature is actually valid.
# NB 1: For 256-bit ECDSA, r & s are 32 byte values. However, due to DER
# encoding quirks (and Satoshi quirks), the values can be 30-34 bytes.
# NB 2: This code, strictly speaking, shouldn't handle the initial size byte or
# the SIGHASH byte. A revision for a future HW problem....
# The format is:
#   Length of signature (not part of the X9.62 sig - 1 byte - Must be 67-75)
#   0x30  (1 byte - "ASN.1 SEQUENCE" byte)
#   Length of "r" & "s" segments  (1 byte - Must be 64-70)
#   0x02  (1 byte - "ASN.1 INTEGER" byte)
#   Length of "r" variable  (1 byte - Must be 30-34)
#   "r" variable  (31-33 bytes)
#   0x02  (1 byte - "ASN.1 INTEGER" byte)
#   Length of "s" variable  (1 byte - Must be 30-34)
#   "s" variable  (31-33 bytes)
#   The OP_CHECKSIG "SIGHASH" byte (not part of the X9.62 sig - 1 byte)
# Input: BinaryUnpacker object pointing to a supposed ECDSA signature. The
#        object will be rewound to its starting position at the end.
# Output: 0 if the key's invalid, or the valid key's overall length (72-74).
def isSig(sigIn):
    '''Determine if a data chunk is an ECDSA signature (X9.62 DER encoding).'''
    retVal = 0
    rewindVal = 0
    sigValid = False
    chunkSize = sigIn.getRemainingSize()

    # Signatures can be 67-75 bytes. We need at least 1 byte to read, at which
    # point the signature will help us determine if we have enough data to read.
    if(chunkSize >= 1):
        initByte = sigIn.get(BINARY_CHUNK, 1)
        sigSize = sigIn.getRemainingSize()
        rewindVal += 1
        if(initByte >= '\x43' and initByte <= '\x4b' and sigSize >= binary_to_int(initByte)):
            if(sigIn.getRemainingSize() >= binary_to_int(initByte)):
                asn1SeqByte = sigIn.get(BINARY_CHUNK, 1)
                rewindVal += 1
                if(asn1SeqByte == ASN1_SEQUENCE):
                    lenByte1 = sigIn.get(BINARY_CHUNK, 1)
                    rewindVal += 1
                    if(lenByte1 >= '\x40' and lenByte1 <= '\x48'):
                        asn1IntByte1 = sigIn.get(BINARY_CHUNK, 1)
                        rewindVal += 1
                        if(asn1IntByte1 == ASN1_INTEGER):
                            rLen = sigIn.get(BINARY_CHUNK, 1)
                            rewindVal += 1
                            if(rLen >= '\x1e' and rLen <= '\x22'):
                                sigIn.advance(binary_to_int(rLen))
                                rewindVal += binary_to_int(rLen)
                                asn1IntByte2 = sigIn.get(BINARY_CHUNK, 1)
                                rewindVal += 1
                                if(asn1IntByte2 == ASN1_INTEGER):
                                    sLen = sigIn.get(BINARY_CHUNK, 1)
                                    rewindVal += 1
                                    if(sLen >= '\x1e' and sLen <= '\x22'):
                                        sigIn.advance(binary_to_int(sLen))
                                        rewindVal += binary_to_int(sLen)
                                        lastByte = sigIn.get(BINARY_CHUNK, 1)
                                        rewindVal += 1
                                        if(isValidSigHashByte(lastByte) == True):
                                            sigValid = True

    # Do final cleanup. Rewind and, if necessary, set the sig size.
    sigIn.rewind(rewindVal)
    if(sigValid == True):
        retVal = binary_to_int(initByte) + 1
    return retVal


# "Shell" function that acts as a starting point for figuring out if a chunk of
# data is an ECDSA, DER-encoded signature. This can handle chunks of data that
# may actually have multiple signatures. If we get up to 3 sigs and there's
# still more data, we'll say the data's valid and assume the user will check the
# remaining data to see if it's valid for any particular purpose.
# Input:  BinaryUnpacker object pointing to a supposed ECDSA signature (it'll be
#         rewound to its starting position at the end) and a boolean flag
#         indicating whether or not the data may be multi-sig.
# Output: 0 if there are no valid sigs, or the number of bytes (from the
#         beginning) that contain actual sigs.
def isSigShell(sigIn, isMultiSig):
    '''Determine if a data chunk contains a valid ECDSA signature (X9.62 DER
       encoding.'''
    validSigs = True
    numSigs = 0
    rewindVal = 0

    # For now, assume valid scripts can have only up to 3 sigs.
    maxNumSigs = 1
    if(isMultiSig == True):
        maxNumSigs = 3

    # While there's data to be read, we believe there are valid sigs, and we
    # haven't encountered more than 3 signatures, 
    while(sigIn.getRemainingSize() != 0 and numSigs < 3 and validSigs == True):
        readByte = sigIn.get(BINARY_CHUNK, 1)
        rewindVal += 1
        if(readByte >= '\x43' and readByte <= '\x4b'):
            sigIn.rewind(1)
            sigAdv = isSig(sigIn)
            if(sigAdv != 0):
                rewindVal += sigAdv
                sigIn.advance(sigAdv)
                numSigs += 1
            else:
                validSigs = False
        else:
            sigIn.rewind(1)
            rewindVal -= 1
            validSigs = False

    # Rewind to where we started and return how many bytes are part of actual
    # sigs.
    sigIn.rewind(rewindVal)
    return rewindVal


# Process TxOut from a Tx. It basically unpacks a TxOut and allows other functs
# to perform more specific tasks. Use it as a starting point!
# Input:  The TxOut object, the TxOut block's hash, the TxOut block's position,
#         the TxOut Tx's index, the TxOut index, and the file where unknown
#         TxOuts will go.
# Output: None
def processTxOut(txOut, blkHash, blkPos, txIdx, txOutIdx, txOutFile):
    '''Function used to start processing of a TxOut object.'''
    advanceVal = 0
    txOutUnpack = BinaryUnpacker(txOut)

    # Simple sanity check before proceeding.
    txOutLen = len(txOut)
    if(txOutLen > 0):
        txOutVal, txOutScrLen, txOutScr, txOutStr = getTxOut(txOutUnpack)
        scrType = processTxOutScr(txOutScr, blkHash, blkPos, txIdx, \
                                  txOutIdx, txOutFile)


# Determines the type of an incoming TxOut script. If it's not any of the five
# standard types (pay-to-pub-key, pay-to-pub-hash, pay-to-script-hash (P2SH -
# BIP16), multisig (BIP11), or OP_RETURN (BC-Core v0.9+)), it's saved to a file.
# Input:  The TxOut object's script, the TxOut block's hash, the TxOut block's
#         position, the TxOut Tx's index, the TxOut index, and the file where
#         unknown TxOuts will go.
# Output: The TxOut type, as defined by class TxType.
def processTxOutScr(txOutScr, blkHash, blkPos, txIdx, txOutIdx, txOutFile):
    '''Function processing a TxOut script.'''
    # Proceed only if there's data to read.
    txOutScrUnpack = BinaryUnpacker(txOutScr)
    retVal = TxType.unknownTx
    txOutScrSize = txOutScrUnpack.getRemainingSize()
    if(txOutScrSize > 0):
        # Read the initial byte and determine what TxOut type it is.
        initByte = txOutScrUnpack.get(BINARY_CHUNK, 1)

        # 0x21/0x41 = Pay2PubKey
        if(initByte == '\x21' or initByte == '\x41'):
            # Make sure it's a valid pub key before declaring it valid.
            pkLen = isPubKey(txOutScrUnpack)
            if(pkLen != 0):
                retVal = TxType.p2pKey

        # OP_DUP = Pay2PubKeyHash
        elif(initByte == OP_DUP):
            # HACK ALERT: Some bright bulb has created OP_* TxOuts that have
            # nothing but the OP_* code. Check the remaining size upfront.
            # (Checking after every read is more robust, really. I'm just lazy
            # and don't want to retrofit this chunk of code. :) )
            if(txOutScrUnpack.getRemainingSize() > 0):
               hashByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
               if(hashByte == OP_HASH160):
                   hashSize = txOutScrUnpack.get(BINARY_CHUNK, 1)
                   hashRemSize = txOutScrUnpack.getRemainingSize()
                   if(hashSize == '\x14' and hashRemSize >= binary_to_int(hashSize)):
                       txOutScrUnpack.advance(binary_to_int(hashSize))
                       eqVerByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
                       if(eqVerByte == OP_EQUALVERIFY):
                           checkSigByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
                           if(checkSigByte == OP_CHECKSIG):
                              retVal = TxType.p2pHash

        # OP_HASH160 = Pay2ScriptHash
        elif(initByte == OP_HASH160):
            hashSize = txOutScrUnpack.get(BINARY_CHUNK, 1)
            hashRemSize = txOutScrUnpack.getRemainingSize()
            if(hashSize == '\x14' and hashRemSize >= binary_to_int(hashSize)):
               txOutScrUnpack.advance(binary_to_int(hashSize))
               eqByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
               if(eqByte == OP_EQUAL):
                  retVal = TxType.p2sh

        # OP_1/2/3 = MultiSig
        elif(initByte == OP_1 or initByte == OP_2 or initByte == OP_3):
            validKeys = True
            readByte = 0
            numKeys = 0

            # HACK ALERT 1: Some scripts are weird and initially appear to be
            # multi-sig but really aren't. We should compensate. One particular
            # way is to require at least 36 bytes (assume 1-of-1 w/ compressed
            # key) beyond the initial byte.
            #
            # HACK ALERT 2: There are some multisig TxOuts that, for unknown
            # reasons have things like compressed keys that where the first byte
            # is 0x00, not 0x02 or 0x03. For now, we just mark them as unknown
            # Tx and move on.
            if(txOutScrUnpack.getRemainingSize() >= 36):
                readByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
                while((readByte == '\x21' or readByte == '\x41') and numKeys < 3
                       and validKeys == True):
                    pkLen = isPubKey(txOutScrUnpack)
                    if(pkLen != 0):
                        txOutScrUnpack.advance(pkLen)
                        numKeys += 1
                        readByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
                    else:
                        validKeys = False
            else:
                validKeys = False
            if(validKeys == True):
                if((readByte == OP_1 or readByte == OP_2 or readByte == OP_3) \
                    and binary_to_int(initByte) <= binary_to_int(readByte)):
                    cmsByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
                    if(cmsByte == OP_CHECKMULTISIG):
                        retVal = TxType.multiSig

        # OP_RETURN = Arbitrary data attached to a Tx.
        # Official as of BC-Core 0.9. https://bitcoinfoundation.org/blog/?p=290
        # and https://github.com/bitcoin/bitcoin/pull/2738 have the details of
        # the initial commit, with https://github.com/bitcoin/bitcoin/pull/3737
        # having the revision down to 40 bytes.
        elif(initByte == OP_RETURN):
            # If the 1st byte is OP_RETURN, as of BC-Core v0.9, there can be
            # arbitrary data placed afterwards. This makes the TxOut immediately
            # prunable, meaning it can never be used as a TxIn. (It can still be
            # spent, mind you.) The final BC-Core 0.9 only accepts <=40 bytes,
            # but preview versions accepted <=80. In theory, any amount of data
            # is valid, but miners won't accept non-standard amounts by default.
            #
            # Anyway, since it's arbitrary, we don't care what's present and
            # just assume it's valid.
            retVal = TxType.opReturn

        # Everything else is weird and should be reported.
        else:
            print("DEBUG: Block {0} - Tx Hash {1}: 1st BYTE (TxOut) IS " \
                  "TOTALLY UNKNOWN!!! BYTE={2}".format(blkPos, \
                  binary_to_hex(curTxHash, endOut=BIGENDIAN), \
                  binary_to_hex(initByte)))

    # Write the script to the file if necessary.
    if(retVal == TxType.unknownTx):
        print("TxOut:        {0}".format(binary_to_hex(txOutScr)), \
              file=txOutFile)
        print("Block Number: {0}".format(blkPos), file=txOutFile)
        print("Block Hash:   {0}".format(binary_to_hex(blkHash)), \
              file=txOutFile)
        print("Tx Hash:     {0}", binary_to_hex(curTxHash, endOut=BIGENDIAN), \
                                                file=txOutFile)
        print("Tx Index:     {0}", txIdx, file=txOutFile)
        print("TxOut Index:  {0}", txOutIdx, file=txOutFile)
        print("---------------------------------------", file=txOutFile)

    return retVal


# Process TxIn from a Tx. It basically unpacks a TxIn and allows other functs to
# perform more specific tasks. Coinbase TxIns are ignored. Use this function as
# a starting point!
# Input:  The TxIn object, the TxIn block's hash, the TxIn block's position, the
#         TxIn Tx's index, the TxIn index, and the file where unknown TxIns will
#         go.
# Output: None
def processTxIn(txIn, blkHash, blkPos, txIdx, txInIdx, txInFile):
    '''Function used to start processing of a TxIn object.'''
    advanceVal = 0
    txInUnpack = BinaryUnpacker(txIn)

    # Simple sanity check before proceeding.
    txInLen = len(txIn)
    if(txInLen > 0):
        txInPrevHash, txInPrevTxOutHashIdx, txInScrLen, txInScr, txInSeqNum, \
        txInStr = getTxIn(txInUnpack)

        # Proceed only if there's a script and if this isn't a coinbase TxIn.
        # For now, assume it's coinbase if the hash of the referenced TxOut
        # is a 32-byte NULL object.
        if(txInScrLen != 0 and txInPrevHash != ('\x00' * 32)):
            scrType = processTxInScr(txInScr, blkHash, blkPos, txIdx, \
                                      txInIdx, txInFile)


# Process TxIn from a Tx. Determines which TxIn type it is. If it's not any of
# the four standard types (pay-to-pub-key, pay-to-pub-hash, pay-to-script-hash
# (P2SH - BIP16), multisig (BIP11)), or if it's a P2SH script, it's saved to a
# file. (The OP_RETURN script type has no use for TxIns.) P2SH TxIn scripts are
# saved because the scripts inside the TxIn, as of Apr. 2014, are never
# standard TxOut scripts.
# Input: TxIn length, TxIn, the TxIn block's hash, the TxIn block's position,
# the TxIn Tx's index, the TxIn index, and the file where unknown TxIns will go.
# Output: The TxIn type, as defined by class TxType.
def processTxInScr(txInScr, blkHash, blkPos, txIdx, txInIdx, txInFile):
    '''Function processing a TxIn script.'''
    # Proceed only if there's data to read.
    txInScrUnpack = BinaryUnpacker(txInScr)
    retVal = TxType.unknownTx
    txInScrSize = txInScrUnpack.getRemainingSize()
    if(txInScrSize > 0):
        # Read the initial byte and determine what TxOut type it is.
        initByte = txInScrUnpack.get(BINARY_CHUNK, 1)

        # Except for multisig and possibly OP_RETURN, all should start with a
        # sig.
        if(initByte >= '\x43' and initByte <= '\x4b'):
            # Make sure it's a valid pub key before declaring it valid.
            # CATCH: We'll rewind because the first byte of the sig isn't
            # repeated, meaning the stack uses the first byte of the sig to push
            # the rest of the sig onto the stack. The rewind isn't necessary but
            # I'd like to keep the sig verification whole.
            txInScrUnpack.rewind(1)
            sigLen = isSigShell(txInScrUnpack, False)
            if(sigLen != 0):
                txInScrUnpack.advance(sigLen)
                if(txInScrUnpack.getRemainingSize() == 0):
                    retVal = TxType.p2pKey
                else:
                    readByte = txInScrUnpack.get(BINARY_CHUNK, 1)
                    if(readByte == '\x21' or readByte == '\x41'):
                        pkLen = isPubKey(txInScrUnpack)
                        if(pkLen != 0):
                            retVal = TxType.p2pHash

        # OP_0 = P2SH or MultiSig
        elif(initByte == OP_0):
            numBytesAdv = isSigShell(txInScrUnpack, True)

            # Proceed only if there was at least 1 valid sig.
            if(numBytesAdv != 0):
                txInScrUnpack.advance(numBytesAdv)
                numBytesRem = txInScrUnpack.getRemainingSize()
                if(numBytesRem != 0):
                    # Confirm that the remaining bytes are a standard script
                    # before marking this as a P2SH script. (There are P2SH
                    # scripts that aren't standard, so we'll mark the entire
                    # script as unknown and save it.) In a fully robust system,
                    # we'd Hash160 and compare against the Hash160 in the
                    # ref'd TxOut to confirm that this is valid.
                    # NB: In the real world, it looks like all scripts don't
                    # match the normal TxOut types! Just mark this as P2SH and
                    # write it out anyway.
#                    p2shScript = txInScrUnpack.get(BINARY_CHUNK, numBytesRem)
#                    if(processTxOutScr(p2shScript, blkHash, blkPos, txIdx, \
#                                       txOutIdx, txOutFile) != TxType.unknownTx):
#                        retVal = TxType.p2sh
#                        print("HEY, WE GOT A GOOD SCRIPT! {0}".format(binary_to_hex(p2shScript)))
#                    else:
#                        print("OH NO, WE HAVE A BAD SCRIPT! {0}".format(binary_to_hex(p2shScript)))
                    retVal = TxType.p2sh
                else:
                    # We have multi-sig.
                    retVal = TxType.multiSig

        # We have an unknown script type. We'll report it. There's a chance it
        # refers to an OP_RETURN TxOut script but we'll ignore that possibility
        # for now in order to keep things simple.
        else:
            print("DEBUG: Block {0}: 1st BYTE (TxIn) IS TOTALLY UNKNOWN!!! " \
                  "BYTE={1}".format(blkPos, binary_to_hex(initByte)))

    # If a script is unknown or is P2SH, write it out here.
    # NB: After running this code several times, it appears that the multisig
    # code uses keys with invalid first bytes. I'm not sure what's going on. The
    # scripts seem valid otherwise.
#    if(retVal == TxType.unknownTx or retVal == TxType.p2sh):
#        if(retVal == TxType.p2sh):
#            print("P2SH script")
#        else:
#            print("Unknown TxIn script")
    if retVal == TxType.unknownTx:
        print("TxIn:         {0}".format(binary_to_hex(txInScr)), \
              file=txInFile)
        print("Block Number: {0}".format(blkPos), file=txInFile)
        print("Block Hash:   {0}".format(binary_to_hex(blkHash)), \
              file=txInFile)
        print("Tx Hash:     {0}", binary_to_hex(curTxHash, endOut=BIGENDIAN), \
                                                file=txInFile)
        print("Tx Index:     {0}", txIdx, file=txInFile)
        print("TxIn Index:   {0}", txInIdx, file=txInFile)
        print("---------------------------------------", file=txInFile)

    return retVal


if __name__ == '__main__':
    # Variables
#    curBlkFile = 138 ################################################################## ONLY IN SPECIAL CIRCUMSTANCES
    curBlkFile = 0
    numBlks = 0
    fileName = getBCBlkFilename(curBlkFile)

    # Open a file which will receive the TxOut materials.
    txInFilename = "prob3TxIn.txt"
    txInFile = open(txInFilename, "wt")
    txOutFilename = "prob3TxOut.txt"
    txOutFile = open(txOutFilename, "wt")

    # Write the starts of the TxOut/TxIn files.
    print("Unknown TxOuts", file=txOutFile)
    print("---------------------------------------", file=txOutFile)
    print("Unknown/P2SH TxIns", file=txInFile)
    print("---------------------------------------", file=txInFile)

    # Iterate through each block by going through each file. Note that the code
    # assumes blocks are in order. In the future, this may not be case.
    while(os.path.isfile(fileName) is True):
#    if(os.path.isfile(fileName) == True): # SPECIAL DEBUG: ONLY 1 FILE PARSED
        print("DEBUG: File blk%05d.dat exists." % curBlkFile)

        # While reading the files, read data only as needed, and not all at
        # once. More I/O but it keeps memory usage down.
        with open(fileName, "rb") as rawData:
            try:
                # Read the magic bytes (4 bytes) & block size (4 bytes). Proceed
                # only if there's data to read.
                readData = rawData.read(8)
                while(readData != ""):
                    # If the magic bytes are legit, proceed.
                    readUnpack = BinaryUnpacker(readData)
                    read_magic = readUnpack.get(BINARY_CHUNK, 4)
                    if(read_magic == MAGIC_BYTES):
                        # Get the block header data.
                        blockLen = readUnpack.get(UINT32)
                        blockVer, prevBlkHash, merkRoot, timestamp, bits, \
                        nonce, blkHdrHash = getBlkHdrValues(rawData)

                        # Get the transaction data and process it.
                        rawTxData = rawData.read(blockLen - 80)
                        txUnpack = BinaryUnpacker(rawTxData)
                        txVarInt = txUnpack.get(VAR_INT)
                        txIdx = 0

                        # Process all Tx objects.
                        while(txVarInt > 0):
                            txVer, numTxIn, txInList, numTxOut, txOutList, \
                            txLockTime, txHash = getTxObj(txUnpack)
                            curTxHash = txHash  # Global hack 'cause I'm lazy.

                            # Process every TxOut & TxIn in a Tx.
                            txOutIdx = 0
                            txInIdx = 0
                            for txOutObj in txOutList:
                                processTxOut(txOutObj, blkHdrHash, numBlks, \
                                             txIdx, txOutIdx, txOutFile)
                                txOutIdx += 1
                            for txInObj in txInList:
                                processTxIn(txInObj, blkHdrHash, numBlks, \
                                             txIdx, txInIdx, txInFile)
                                txInIdx += 1

                            txIdx += 1
                            txVarInt -= 1

                        # Increment the # of blocks we've processed.
                        numBlks += 1

                    # If magic bytes aren't magic, assume we've hit the
                    # end. In theory, Bitcoin-Qt pre-buffers w/ 0s, but
                    # in practice, the pre-buffering seems to be anything.
                    else:
                        break

                    # Before looping back, try reading data again.
                    readData = rawData.read(8)

            # Always close a file once it's done.
            finally:
                rawData.close()

        # Get ready to read the next file.
        curBlkFile += 1
        fileName = getBCBlkFilename(curBlkFile)

    txInFile.close()
    txOutFile.close()
