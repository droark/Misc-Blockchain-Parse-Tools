# (c) 2016 Douglas Roark
# Licensed under the MIT License. See LICENSE for the details.

from __future__ import print_function, division # Valid as of 2.6
import sys
sys.path.insert(0, '/home/droark/Projects/etotheipi-BitcoinArmory')
import binascii, hashlib, string, os, resource
from collections import namedtuple
from math import ceil, log
from copy import deepcopy
from collections import defaultdict

from armoryengine.BinaryUnpacker import * # Armory
from armoryengine.BinaryPacker import * # Armory
from armoryengine.ArmoryUtils import * # Armory

preBufZero = '\x00' * 4
prevTxZero = '\x00' * 32

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
# Note that NULL_BYTE isn't official. I added it due to code quirks.
NULL_BYTE            = '\x00' # A few sig/pubKey combos use a null byte.
SIGHASH_ALL          = '\x01'
SIGHASH_NONE         = '\x02'
SIGHASH_SINGLE       = '\x03'
SIGHASH_ANYONECANPAY = '\x80'

# ASN.1 encoding bytes
ASN1_INTEGER  = '\x02'
ASN1_SEQUENCE = '\x30'

# Quick-and-dirty enum.
class TxType:
    p2pKey    = 1
    p2pHash   = 2
    p2sh      = 3
    multiSig  = 4
    opReturn  = 5
    unknownTx = 6

# A global variable 'cause I'm being a lazy bastard. :) Used when printing data
# about a weird transaction. Useful for blockchain.info, blockexplorer.com, etc.
curTxHash = '\x00'

# A class that contains some information about a TxOut object. In particular, it
# carries the TxOut value, a boolean indicating if the TxOut has been used, and
# a binary string representing an address for the TxOut object.
class txOutDictObj(object):
    def __init__(self):
        self.txOutVal = 0
        self.txOutUsed = False
        self.txOutAddr = '\x00'

    def getVals(self):
        return [self.txOutVal, self.txOutUsed, self.txOutAddr]

    def setVals(self, inTxOutVal, inTxOutUsed, inTxOutAddr):
        self.txOutVal = inTxOutVal
        self.txOutUsed = inTxOutUsed
        self.txOutAddr = inTxOutAddr

    def markAsUsed(self):
        self.txOutUsed = True


# A class that contains some information about a Bitcoin address. In particular,
# it contains the current balance and the total number of coins received.
class addrMapDictObj(object):
    def __init__(self):
        self.curBal = 0
        self.totRcvd = 0

    def getVals(self):
        return [self.curBal, self.totRcvd]

    def addBal(self, inCurBal):
        self.curBal += inCurBal
        self.totRcvd += inCurBal

    def reduceBal(self, amt):
        self.curBal -= amt


# Global vars
# http://stackoverflow.com/questions/5029934/python-defaultdict-of-defaultdict
# shows how to put a defaultdict inside a defaultdict. Basically, a defaultdict
# needs a callable argument when trying to find a non-existent key, passing back
# the default value as the key's value. A lambda is callable. This is a good way
# to place a defaultdict inside a defaultdict.
prevTxMap = defaultdict(lambda : defaultdict(txOutDictObj))
addrMap = defaultdict(addrMapDictObj)
part1AddrB58Str = "12cbQLTFMXRnSzktFkuoG3eHoMeFtpTu3S"
part1AddrB58 = base58_to_binary(part1AddrB58Str)
armoryAddrB58Str = "1ArmoryXcfq7TnCSuZa9fQjRYwJ4bkRKfv"
armoryAddrB58 = base58_to_binary(armoryAddrB58Str)
testNetByte = "6f"
mainNetByte = "00"
deleteUsedTxOuts = False  # False for Parts 1 & 2, True for Part 3
checkStr = part1AddrB58Str  # Part 1 for Part 1, Armory for Part 2

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
# tansaction. The inputs & outputs will be returned in lists.
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


# Process TxOut from a Tx. It basically unpacks a TxOut and allows other functs
# to perform more specific tasks. Use it as a starting point!
# Input:  The TxOut object, the TxOut block's hash, the TxOut block's position,
#         the TxOut Tx's index, the TxOut index, and the 2xSHA256 hash of the
#         transaction.
# Output: None
def processTxOut(txOut, blkHash, blkPos, txIdx, txOutIdx, txHash):
    '''Function used to start processing of a TxOut object.'''
    advanceVal = 0
    txOutUnpack = BinaryUnpacker(txOut)

    # Simple sanity check before proceeding.
    txOutLen = len(txOut)
    if(txOutLen > 0):
        txOutVal, txOutScrLen, txOutScr, txOutStr = getTxOut(txOutUnpack)
        scrAddr = processTxOutScr(txOutScr, blkHash, blkPos, txIdx, \
                                  txOutIdx)

        # Create a TxOut defaultdict entry for each TxOut entry.
        # Create an address entry for each address.
        prevTxMap[txHash][txOutIdx].setVals(txOutVal, False, scrAddr)
        myAddrMapObj = addrMap[scrAddr]
        myAddrMapObj.addBal(txOutVal)

        # Every time a Base58 string we're checking gets coins, make a note.
        # if(scrAddr == checkStr):
        #     print("{0} received money in block {1} - Tx #{2} - TxOut #{3} - " \
        #           "{4} BTC".format(checkStr, blkPos, txIdx, txOutIdx, \
        #                            (txOutVal / 100000000)))


# Process TxIn from a Tx. It basically unpacks a TxIn and allows other functs to
# perform more specific tasks. Coinbase TxIns are ignored. Use this function as
# a starting point!
# Input:  The TxIn object, the TxIn block's hash, the TxIn block's position, the
#         TxIn Tx's index, the TxIn index, the 2xSHA256 hash of the transaction,
#         and a flag indicating if a used TxOut should be deleted.
# Output: None
def processTxIn(txIn, blkHash, blkPos, txIdx, txInIdx, txHash, delUsedTxOuts):
    '''Function used to start processing of a TxIn object.'''
    advanceVal = 0
    txInUnpack = BinaryUnpacker(txIn)

    # Simple sanity check before proceeding.
    txInLen = len(txIn)
    if(txInLen > 0):
        txInPrevTxOutHash, txInPrevTxOutHashIdx, txInScrLen, txInScr, \
        txInSeqNum, txInStr = getTxIn(txInUnpack)

        # Get info on the referenced TxOut and use it to update the address's
        # balance if it hasn't already been used.
        if txInPrevTxOutHash != prevTxZero:
            refTxOutObj = prevTxMap[txInPrevTxOutHash][txInPrevTxOutHashIdx]
            [refVal, refUsed, refAddr] = refTxOutObj.getVals()
            if not refUsed:
                # Do we want to delete the TxOut or just mark it as used?
                if delUsedTxOuts:
                    del prevTxMap[txInPrevTxOutHash][txInPrevTxOutHashIdx]
                else:
                    refTxOutObj.markAsUsed()

                myAddrMapObj = addrMap[refAddr]
                myAddrMapObj.reduceBal(refVal)

                # Every time a Base58 string we're checking gets coins, make a note.
                # if(scrAddr == checkStr):
                #     print("{0} spent money in block {1} - Tx #{2} - TxIn " \
                #           "#{3} - {4} BTC".format(checkStr, blkPos, txIdx, \
                #                                   txInIdx, (refVal / 100000000)))


# Determines the type of an incoming TxOut script and then returns an address
# value. The value that is returned is defined as follows:
# Pay-to-pub-key - The public key as a Base58 address
# Pay-to-pub-hash - The pub key hash as a Base58 address
# Pay-to-script-hash - The script hash
# Multisig - All the pub keys in the set
# OP_RETURN - Everything after the OP_RETURN
# Non-standard scripts - The entire script contents.
# Unless otherwise noted, the code will assume the contents of the various
# script types are what we're told they are, and we will return address values
# that may or may not be actual keys or whatever. This is a horrible idea in a
# production setting. For homework, this is basically okay. :) Any exceptions
# will be noted. One such exception is a blank return value
# Input:  The TxOut object's script, the TxOut block's hash, the TxOut block's
#         position, the TxOut Tx's index, and the TxOut index.
# Output: The TxOut address as previously defined in the function description.
def processTxOutScr(txOutScr, blkHash, blkPos, txIdx, txOutIdx):
    '''Function processing a TxOut script.'''
    # Proceed only if there's data to read.
    retVal = txOutScr
    txOutScrUnpack = BinaryUnpacker(txOutScr)
    txOutAddress = BinaryPacker()
    txType = TxType.unknownTx
    txOutScrSize = txOutScrUnpack.getRemainingSize()

    if(txOutScrSize > 0):
        # Read the initial byte and determine what TxOut type it is.
        initByte = txOutScrUnpack.get(BINARY_CHUNK, 1)

        # 0x21/0x41 = Pay2PubKey
        if(initByte == '\x21' or initByte == '\x41'):
            # Make sure it's a valid pub key before declaring it valid.
            pkLen = isPubKey(txOutScrUnpack)
            if(pkLen != 0):
                # Save the pub key.
                txOutKey = txOutScrUnpack.get(BINARY_CHUNK, pkLen)
                txOutAddress.put(BINARY_CHUNK, txOutKey)
                txType = TxType.p2pKey

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
                    if(hashSize == '\x14' and \
                       hashRemSize >= binary_to_int(hashSize)):
                        txOutHash = txOutScrUnpack.get(BINARY_CHUNK, \
                                                       binary_to_int(hashSize))
                        # Save the hash.
                        txOutAddress.put(BINARY_CHUNK, txOutHash)
                        eqVerByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
                        if(eqVerByte == OP_EQUALVERIFY):
                            checkSigByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
                            if(checkSigByte == OP_CHECKSIG):
                                txType = TxType.p2pHash

        # OP_HASH160 = Pay2ScriptHash
        elif(initByte == OP_HASH160):
            hashSize = txOutScrUnpack.get(BINARY_CHUNK, 1)
            hashRemSize = txOutScrUnpack.getRemainingSize()
            if(hashSize == '\x14' and hashRemSize >= binary_to_int(hashSize)):
                txOutHash = txOutScrUnpack.get(BINARY_CHUNK, \
                                               binary_to_int(hashSize))
                # Save the hash.
                txOutAddress.put(BINARY_CHUNK, txOutHash)
                eqByte = txOutScrUnpack.get(BINARY_CHUNK, 1)
                if(eqByte == OP_EQUAL):
                    txType = TxType.p2sh

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
                        txOutKey = txOutScrUnpack.get(BINARY_CHUNK, pkLen)
                        # Save the key.
                        txOutAddress.put(BINARY_CHUNK, txOutKey)
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
                        txType = TxType.multiSig

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
            # just assume it's valid. Save all the data as the TxOut address.
            opRetData = txOutScrUnpack.get(BINARY_CHUNK, \
                                           txOutScrUnpack.getRemainingSize())
            # Save the data.
            txOutAddress.put(BINARY_CHUNK, opRetData)
            txType = TxType.opReturn

        # Everything else isn't standard. For now, we'll do nothing.
        # else:
        #     print("DEBUG: 1st BYTE (TxOut) IS TOTALLY UNKNOWN!!! BYTE={0}".format(binary_to_hex(initByte)))

    # Could it be that there is no TxOut script? Is this legal? Let's take a
    # peek and write some debug code.
    else:
        print("DEBUG: At block {0}, we have an empty TxOut script!".format(blkPos))

    # If we have a known TxOut type, we'll return an address instead of the
    # entire TxOut script. Note that it's unlikely but possible that an address
    # value for, say, OP_RETURN could match a pub key hash. In production code,
    # we'd want to add extra data to ensure that no collisions have occurred
    # (e.g., 2 different addresses are sharing a common balance), or possibly
    # use a different approach altogether.
    if(txType != TxType.unknownTx):
        retVal = txOutAddress.getBinaryString()
        if(txType == TxType.p2pKey):
            step1 = hash160(retVal)
            step2 = hash160_to_addrStr(step1)
            retVal = base58_to_binary(step2)
        elif(txType == TxType.p2pHash):
            step1 = hash160_to_addrStr(retVal)
            retVal = base58_to_binary(step1)

    return retVal


if __name__ == '__main__':
    # Variables
    curBlkFile = 0
    numBlks = 0
    fileName = getBCBlkFilename(curBlkFile)

    # Iterate through each block by going through each file. Note that the code
    # assumes blocks are in order. In the future, this may not be case.
    # while(os.path.isfile(fileName) is True):
    for fileNum in range(0, 1): # SPECIAL DEBUG: Only the first few files are parsed
        print("DEBUG: File blk%05d.dat is being processed." % curBlkFile)

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

                            # Process every TxOut & TxIn in a Tx. A TxOut can be
                            # spent in the same block where it's created, so
                            # let's process the TxOuts first.
                            txOutIdx = 0
                            txInIdx = 0
                            for txOutObj in txOutList:
                                processTxOut(txOutObj, blkHdrHash, numBlks, \
                                             txIdx, txOutIdx, txHash)
                                txOutIdx += 1
                            for txInObj in txInList:
                                processTxIn(txInObj, blkHdrHash, numBlks, \
                                            txIdx, txInIdx, txHash, \
                                            deleteUsedTxOuts)
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

    # Print final amounts and such.
    # PARTS 1 & 2
    # myAddrMapObj = addrMap[checkStr]
    # [finalBal, finalRcvdAmt] = myAddrMapObj.getVals()
    # print("The total amount received by address {0} is {1} " \
    #       "BTC".format(checkStr, (finalRcvdAmt / 100000000)))

    # PART 3 - To get an accurate count, we must get the length of the
    # defauldict objs inside the prevTxMap defaultdict.
    divMaxRSS = 1000
    if OS_MACOSX:
        divMaxRSS = 1000000
    totalUTXOs = 0
    for indices in prevTxMap:
        totalUTXOs += len(prevTxMap[indices])
    print("The total number of UTXOs is {0}".format(totalUTXOs))
    print("The amount of memory used by this program is {0} " \
          "MB.".format(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / divMaxRSS))
