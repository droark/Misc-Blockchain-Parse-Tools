# (c) 2016 Douglas Roark
# Licensed under the MIT License. See LICENSE for the details.

from __future__ import print_function, division # Valid as of 2.6
import sys
sys.path.insert(0, '/home/droark/Projects/BitcoinArmory')
import binascii, hashlib, string, os
from collections import namedtuple
from math import ceil, log
from copy import deepcopy
from armoryengine.BinaryPacker import * # Armory
from armoryengine.BinaryUnpacker import * # Armory
from armoryengine.ArmoryUtils import * # Armory

preBufZero = '\x00\x00\x00\x00'

# Get a block file name based on a given number (blkXXXXX.dat).
# Input: A number between 0-99,999.
# Output: Block file name based on the input (e.g., blk00008.dat).
def getBCBlkFilename(fileNum):
    '''Create a Bitcoin block data file name based on the incoming number.'''
    if(fileNum < 0 or fileNum > 99999):
        print("Bad blkXXXXX.dat input number. Defaulting to blk99999.dat.")
        fileNum = 99999
    blkFile = os.path.join(BLKFILE_DIR, 'blk%05d.dat' % fileNum)
    print("DOUG DEBUG: blkFile={0}".format(blkFile))
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

# Find the Merkle root for a given set of SHA256 inputs.
# Input: A list with all incoming (binary) hashes for the Merkle tree.
# Output: A 2xSHA256 hash with the tree's root.
def find_merkle_root(in_hashes):
    '''Function that takes a list of SHA256 hashes of transactions and
       calculates the merkle root. Result is binary (non-printable data.)'''

    # Do some initial error checking
    if len(in_hashes) < 1:
        print("Please provide at least 1 hash!")
        return 0

    # Initial setup
    tree_levels_ceil = int(ceil(log(len(in_hashes), 2)))
    tree_levels_floor = tree_levels_ceil - 1

    # Create a deep copy of the hashes and prepare to alter them as needed.
    hash_vals = deepcopy(in_hashes)
    results = []
    hash_vals = [hex_vals for hex_vals in hash_vals]

    # Iterate through each level of the tree. Concatenate, duplicate the final
    # entry in the row if the row has an odd # of elements, then hash.
    while tree_levels_floor >= 0:
        if((len(hash_vals) % 2) == 1):
            hash_vals.append(hash_vals[-1])
#            print("DEBUG: New hash val len={0}".format(len(hash_vals)))
        for i in xrange(len(hash_vals) // 2):
            concat = hash_vals[i*2] + hash_vals[(i*2)+1]
            results.append(hash256(concat))
#            print("DEBUG: Hash result for iteration {0}={1}".format(i, binary_to_hex(results[i])))

        # Move everything over to hash_vals and prepare for the next round
        hash_vals = deepcopy(results)
        results = []
        tree_levels_floor -= 1
#        print("DEBUG: Hash val len={0}".format(len(hash_vals)))

    # We have the merkle hash now! Return it as a binary (non-printable) val.
    return hash_vals[0]

# Look in a BinaryUnpacker object with a transaction input item and gets the
# pieces. The transaction input includes, in the following order:
# 1)A 2xSHA256 hash of a transaction being used as an input. (32 bytes - BE)
# 2)The index of the referenced output in the referenced trans.  (4 bytes - LE)
# 3)Transaction input's script length.  (VAR_INT - Little endian)
# 4)Transaction input's script.  (VAR_LEN - Big endian)
# 5)Sequence # (usually 0xFFFFFFFF, usually irrelevant).  (4 bytes - LE)
# Input: A BinaryUnpacker object with the transaction input.
# Output: The transaction input's individual objects.
def getTxInput(txUnpack):
    '''Function that unpacks the items inside a transaction input.'''
    txInPrevHash = txUnpack.get(BINARY_CHUNK, 32) # BE
    txInPrevTxOutHashIdx = txUnpack.get(UINT32)
    txInScrLen = txUnpack.get(VAR_INT)
    txInScr = txUnpack.get(BINARY_CHUNK, txInScrLen)
    txInSeqNum = txUnpack.get(UINT32)
    return (txInPrevHash, txInPrevTxOutHashIdx, txInScrLen, txInScr, txInSeqNum)

# Function that takes transaction input objects and creates a binary string
# representing the input.
# Input: Transaction input's prev hash, prev hash idx, script len, script, and
#        sequence #.
# Output: A binary string representing the transaction input.
def getTxInStr(txInPrevHash, txInPrevTxOutHashIdx, txInScrLen, txInScr, \
               txInSeqNum):
    '''Function that creates a transaction input from the function inputs.'''
    txInBin = BinaryPacker()
    txInBin.put(BINARY_CHUNK, txInPrevHash)
    txInBin.put(UINT32, txInPrevTxOutHashIdx)
    txInBin.put(VAR_INT, txInScrLen)
    txInBin.put(BINARY_CHUNK, txInScr)
    txInBin.put(UINT32, txInSeqNum)
    return txInBin.getBinaryString()

# Look in a BinaryUnpacker object with a transaction output item and gets the
# pieces. The transaction output includes, in the following order:
# 1)The amount sent in the transaction.  (8 bytes - LE)
# 2)Transaction output's script length.  (VAR_INT - LE)
# 3)Transaction output's script.  (VAR_LEN - BE)
# Input: A BinaryUnpacker object with the transaction input.
# Output: The transaction input's individual objects.
def getTxOutput(txUnpack):
    '''Function that unpacks the items inside a transaction output.'''
    txOutVal = txUnpack.get(UINT64)
    txOutScrLen = txUnpack.get(VAR_INT)
    txOutScr = txUnpack.get(BINARY_CHUNK, txOutScrLen)
    return (txOutVal, txOutScrLen, txOutScr)

# Function that takes transaction output objects and creates a binary string
# representing the output.
# Input: Transaction output's output amount, script len, and script.
# Output: A binary string representing the transaction output.
def getTxOutStr(txOutVal, txOutScrLen, txOutScr):
    '''Function that creates a transaction output from the function inputs.'''
    txOutBin = BinaryPacker()
    txOutBin.put(UINT64, txOutVal)
    txOutBin.put(VAR_INT, txOutScrLen)
    txOutBin.put(BINARY_CHUNK, txOutScr)
    return txOutBin.getBinaryString()

# Look in a BinaryUnpacker object with a transaction item and gets the pieces.
# The transaction includes, in the following order:
# 1)Transaction version number. (4 bytes - Little endian)
# 2)Number of transaction inputs. (VAR INT - LE)
# 3)Transaction inputs. (VAR_LEN - Big endian)
# 4)Number of transaction outputs. (VAR INT - LE)
# 5)Transaction outputs. (VAR_LEN - BE)
# 6)Transaction lock time. (4 bytes - LE)
# Input: A BinaryUnpacker object with the transaction.
# Output: The transaction's individual objects. The inputs & outputs will be
#         returned in lists.
def getTxObj(txUnpack):
    '''Function that unpacks the items inside a transaction.'''
    txInList = []
    txOutList = []
    txInStr = b''
    txOutStr = b''

    # Get the Tx version and the inputs. Put the items in a list.
    txVer = txUnpack.get(UINT32) # Item 1
    numTxIn = txUnpack.get(VAR_INT) # Item 2
    txInCtr = numTxIn
    while(txInCtr > 0):
        txInPrevHash, txInPrevTxOutHashIdx, txInScrLen, txInScr, txInSeqNum = \
            getTxInput(txUnpack) # Item 3
        txInStr = getTxInStr(txInPrevHash, txInPrevTxOutHashIdx, txInScrLen, \
                             txInScr, txInSeqNum)
        txInList.append(txInStr)
        txInCtr -= 1

    # Get the Tx outputs and put them in a list.
    numTxOut = txUnpack.get(VAR_INT) # Item 4
    txOutCtr = numTxOut
    while(txOutCtr > 0):
        txOutVal, txOutScrLen, txOutScr = getTxOutput(txUnpack) # Item 5
        txOutStr = getTxOutStr(txOutVal, txOutScrLen, txOutScr)
        txOutList.append(txOutStr)
        txOutCtr -= 1

    # Get the Tx lock time, then return everything.
    txLockTime = txUnpack.get(UINT32) # Item 6
    return (txVer, numTxIn, txInList, numTxOut, txOutList, txLockTime)

# Function that takes transaction objects and creates a binary string
# representing the transaction.
# Input: Transaction's ver, # of inputs, input list, # of outputs, output list,
#        and lock time.
# Output: A 2xSHA256 hash of the transaction.
def getTxHash(txVer, numTxIn, txInList, numTxOut, txOutList, txLockTime):
    '''Function that creates a 2xSHA256 hash of a transaction.'''
    txHashBin = BinaryPacker()
    txHashBin.put(UINT32, txVer)
    txHashBin.put(VAR_INT, numTxIn)
    for txIn in txInList:
        txHashBin.put(BINARY_CHUNK, txIn)
    txHashBin.put(VAR_INT, numTxOut)
    for txOut in txOutList:
        txHashBin.put(BINARY_CHUNK, txOut)
    txHashBin.put(UINT32, txLockTime)
    return hash256(txHashBin.getBinaryString())

# Function that determines the number of bytes required to hold a given int.
# Input: Integer whose number of bytes we wish to find.
# Output: The number of bytes needed to hold the int.
def bytesInInt(n):
    '''Function that determines how many bytes are used to hold a given int.'''
    # Use log256 to determine the # of bytes. 2 points:
    # 1)0 is a special case. Return 1.
    # 2)Add 1 to the result. Using int() always rounds down the converted value
    #   (e.g., int(1.99) = 1), so this is safe.
    if n == 0:
        return 1
    return int(log(n, 256)) + 1

# Convert an integer into a Bitcoin difficulty value used in the block header.
# Input: An integer up to (2^224) - 1
# Output: A 32-bit value with the compressed "bits" value for a block header.
def convIntToDiff(intVal):
    '''Convert an integer into a Bitcoin difficulty value.'''
    appendZero = False

    # Figure out how many bits are required to hold the int. Then, get the 1-3
    # most significant bytes.
    numBytes = bytesInInt(intVal)
    msb = (intVal >> ((numBytes * 8) - 8)) & 0xff
    msb2 = (intVal >> ((numBytes * 8) - 16)) & 0xffff
    msb3 = (intVal >> ((numBytes * 8) - 24)) & 0xffffff

    # The MSB is signed. If >127, the result will take a different path.
    if(msb > 0x7f):
        appendZero = True
        numBytes += 1

    # Create the result. The result depends on the MSB of the incoming int.
    # Result bytes are listed from MSB to LSB.
    # Int MSB >127: # of bytes in resulting int, then 0x00, then the 2 most
    # significant bytes of the incoming value.
    # Int MSB <128: # of bytes in resulting int, then the 3 most significant
    # bytes of the incoming value.
    retVal = (numBytes << 24) & 0xff000000
    if(appendZero == True):
        retVal += msb2
    else:
        retVal += msb3

    return retVal

# Convert a Bitcoin difficulty value used in the block header into an integer.
# Input: A 32-bit value with the compressed "bits" value for a block header.
# Output: An integer up to (2^224) - 1
def convDiffToInt(diffVal):
    '''Convert a Bitcoin difficulty value into an integer.'''
    # The conversion formula is as seen below.
    lsb3 = diffVal & 0xffffff
    msb = (diffVal >> 24) & 0xff
    retVal = lsb3 * (2**(8 * (msb - 3)))
#    print("DOUG DEBUG: LSB3 = {0} MSB = {1} Diff ret = {2}".format(lsb3, msb, retVal))
    return retVal

# Alan's test function to confirm that the Merkle code works.
def testMerkle():
    txAhash = hex_to_binary('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa')
    txBhash = hex_to_binary('bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb')
    txChash = hex_to_binary('cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc')
    answer  = hex_to_binary('d6f226837f442e34974d01825cbac711f4c358d1f564747d3d7203a2d4e94619')
    print("PASSED") if find_merkle_root([txAhash, txBhash, txChash]) == answer else "FAILED"

if __name__ == '__main__':
    # Consts
    bDiff = hex_to_int('00000000FFFF0000000000000000000000000000000000000000000000000000', \
                                                                      BIGENDIAN)
    minTargInt = (2 ** 224) - 1
    targDiffTime = 1209600 # 1209600 secs = 2 weeks

    # Variables
    curBlkFile = 0
    numBlks = 0
    totalTx = 0
    lowestHash = hex_to_binary('00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff', \
                                                                      BIGENDIAN)
    confPrevBlkHash = hex_to_binary('0000000000000000000000000000000000000000000000000000000000000000', \
                                                                      BIGENDIAN)
    lowestHashLoc = 0
    lowestHashDiffFloat = 1.0
    curTarg = minTargInt
    curDiff = 0x1d00ffff
    curDiffFloat = 1.0
    maxDiff = curDiff
    maxDiffFloat = curDiffFloat
    firstDiffTime = 0
    lastDiffTime = 0
    netHashPwr = 0
    fileName = getBCBlkFilename(curBlkFile)
    minBlkToBlk = 0
    minBlkLoc = 0
    maxBlkToBlk = 0
    maxBlkLoc = 0
    totBlkToBlk = 0
    prevBlkTime = 0

    # Open a file which will receive the output.
    outputFile = "prob2Out.txt"
    outF = open(outputFile, "wt")

    # Iterate through each block by going through each file.
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

                        # Make sure the previous block is correct.
                        if(prevBlkHash != confPrevBlkHash):
                            print("ERROR: PREVIOUS BLOCK HASH IN BLOCK {0} " \
                                  "IS WRONG.".format(numBlks), file=outF)
                        confPrevBlkHash = blkHdrHash

                        # Get the transaction data and process it.
                        rawTxData = rawData.read(blockLen - 80)
                        txUnpack = BinaryUnpacker(rawTxData)
                        txVarInt = txUnpack.get(VAR_INT)
                        totalTx += txVarInt
                        txList = []
                        while(txVarInt > 0):
                            txVer, txInLen, txIn, txOutLen, txOut, \
                            txLockTime = getTxObj(txUnpack)
                            txHash = getTxHash(txVer, txInLen, txIn, \
                                               txOutLen, txOut, \
                                               txLockTime)
                            txList.append(txHash)
                            txVarInt -= 1

                        # Calculate & confirm the block's Merkle root.
                        calcMerkRoot = find_merkle_root(txList)
                        if(merkRoot != calcMerkRoot):
                            print("MERKLE CHECK FAILED FOR BLOCK " \
                                  "{0}".format(numBlks), file=outF)

                        # If it's time for a difficulty recalc, do it. Recalc
                        # the diff only if past the genesis block.
                        if((numBlks % 2016) == 0):
                            # Apply special "bootstrap" values at genesis block. 
                            if(numBlks == 0):
                                curTarg = convDiffToInt(bits)
                                prevBlkTime = timestamp

                            # If not at the genesis block, do real calcs.
                            else:
                                # How long did it take to make the previous 2016
                                # blks? (Bitcoin uses an off-by-1 principle.)
                                calcBlkTime = lastDiffTime - firstDiffTime

                                # Difficulty can only increase or decrease
                                # by a factor of 4 in either direction.
                                if(calcBlkTime < 302400):
                                    calcBlkTime = 302400
                                elif(calcBlkTime > 4838400):
                                    calcBlkTime = 4838400

                                # Calc the new difficulty only if diff doesn't
                                # dip below 1.
                                newTarg = curTarg * (calcBlkTime / targDiffTime)
                                if(int(newTarg) < minTargInt):
                                    # Create diff, then get target from diff.
                                    # Less accurate math, but it's how BC works!
                                    curDiff = convIntToDiff(int(newTarg))
                                    curTarg = convDiffToInt(curDiff)
                                    curDiffFloat = minTargInt / curTarg

                                    # Save the new diff if it's smaller (i.e.,
                                    # more difficult) than what we have saved.
                                    if(curDiff < maxDiff):
                                        maxDiffFloat = curDiffFloat
                                else:
                                    curDiff = 0x1d00ffff
                                    curTarg = minTargInt
                                    curTDiffFloat = 1.0

                                # Calc the network hashpower in MHash/s.
                                # https://en.bitcoin.it/wiki/Difficulty has the
                                # formula as hashes/s.
                                numerator = curDiffFloat * (2**48)
                                netHashPwr = numerator / 39321000000000

                                print("At block {0}, difficulty becomes {1} " \
                                      "with a network hashing power of ~{2} " \
                                      "MHash/s".format(numBlks, curDiffFloat, \
                                                       netHashPwr), file=outF)

                            # Always save the 1st timestamp for a given period.
                            firstDiffTime = timestamp

                        # Save the last timestamp for a given time period if
                        # difficulty's about to change.
                        elif((numBlks % 2016) == 2015):
                            lastDiffTime = timestamp

                        # Calculate the difficulty the current block
                        # will satisfy. Confirm the block satisfies the
                        # current system difficulty.
                        hashInt = binary_to_int(blkHdrHash)
                        calcDiff = bDiff / hashInt
#                        print("DEBUG: Block {0} Calcs a difficulty of " \
#                               {1}".format(numBlks, calcDiff))
                        if(curDiffFloat > calcDiff):
                            print("ERROR: BLOCK {0} CALCULATES A DIFFICULTY " \
                                  "{1}, WHICH CAN'T SATISFY DIFFICULTY " \
                                  "{2}".format(numBlks, calcDiff, \
                                               curDiffFloat), file=outF)

                        # If the difficulty's the lowest we've seen, save it.
                        if(calcDiff > lowestHashDiffFloat):
                            lowestHashDiffFloat = calcDiff
                            lowestHash = blkHdrHash
                            lowestHashLoc = numBlks

                        # Save the min/max block-to-block times.
                        curBlkToBlk = timestamp - prevBlkTime
                        totBlkToBlk += curBlkToBlk
                        if(curBlkToBlk > maxBlkToBlk):
                            maxBlkToBlk = curBlkToBlk
                            maxBlkLoc = numBlks
                        if(curBlkToBlk < minBlkToBlk):
                            minBlkToBlk = curBlkToBlk
                            minBlkLoc = numBlks
                        prevBlkTime = timestamp

                        # Finally, increment the # of blocks we've processed.
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

    # Calculate
    avgBlkToBlk = totBlkToBlk / numBlks

    # Once all the files are read, print the final data.
    print("Total number of blocks is {0}".format(numBlks), file=outF)
    print("Total number of transactions is {0}".format(totalTx), file=outF)
    print("Lowest hash is {0} and is for block " \
          "{1}".format(binary_to_hex(lowestHash, BIGENDIAN), \
                       lowestHashLoc), file=outF)
    print("The Lowest hash satisfies difficulty " \
          "{0}".format(lowestHashDiffFloat), file=outF)
    print("Maximum difficulty seen on the network is " \
          "{0}".format(maxDiffFloat), file=outF)
    print("Average block-to-block time is {0} " \
          "sec".format(avgBlkToBlk), file=outF)
    print("Minimum block-to-block time is {0} secs seen from blocks " \
          "{1} to {2}".format(minBlkToBlk, (minBlkLoc - 1), \
                              minBlkLoc), file=outF)
    print("Maximum block-to-block time is {0} secs seen from blocks " \
          "{1} to {2}".format(maxBlkToBlk, (maxBlkLoc - 1), \
                              maxBlkLoc), file=outF)
    outF.close()

################################################################################
# Why is the minimum block-to-block time so low?
# https://en.bitcoin.it/wiki/Block_timestamp briefly discusses how Bitcoin
# handles timestamps. In a nutshell, assuming there are no other issues with the
# block, the block's accepted if its timestamp is greater than the previous 11
# blocks' timestamps, and is less than the network-adjusted time + 2 hours.
# (Network-adjusted time is the median of the differences between the local time
# and the nodes to whom you connect, with the difference checked upon connection
# with said peer. The NAT can't more than 70 minutes off from the local time.)
# The idea appears to be to give miners some room to have a misconfigured time,
# but not so much that they can screw everything up. In particular, it appears
# that Satoshi was trying to strike a balance between looseness in the
# implementation of the protocol and rigidity, the latter of which helps protect
# against various attacks and provides some meaning to the timestamp. ("Hey, why
# is this timestamp 50 years ahead of the previous timestamp?")
#
# Why is a balance being struck? Presumably to protect the notion that a block
# should be mined every 10 minutes. This is reflected in the acceptance
# equation, where the past 11 blocks are checked (i.e., we should go back ~2
# hours in theory). Also, reasonably accurate timestamps are needed to calculate
# new difficulties. If everything's kept within a reasonable band, the
# difficulty calculation should be skewed only by negligible factors since
# outliers tend to cancel each other out over time.
################################################################################
