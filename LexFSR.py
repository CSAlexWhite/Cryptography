import os
import crypto
from crypto import *


class LexFSR:

    def __init__(self, initString):

        self.templist = list()
        self.initString = initString

        if len(initString) < 16:            # make sure there's enough text
                                            # to seed properly
            print('The seed is too short!')

        self.seed = stringToList(getSeed(initString))

        self.lengths = (19, 17, 13, 11, 9, 7, 6, 5, 4, 3)

        self.taps = ((19, 18, 17, 14),      # initialize the taps
                     (17, 14),
                     (13, 12, 11, 8),
                     (11, 9),
                     (9, 5),
                     (7, 6),
                     (6, 5),
                     (5, 3),
                     (4, 3),
                     (3, 2))

        self.machines = list()

        try:

            for i in range(len(self.lengths)):   # initialize the whole machine

                print(i, "\n")
                templist = list()

                for j in range(self.lengths[i]):

                    templist.append(self.seed.pop(0))      

                print("Fill: ", templist)
                print("Taps: ", self.taps[i])

                newLFSR = LFSR(templist, self.taps[i])

                print("First TwentyFive:", newLFSR.putout(25, True, True))

                self.machines.append(newLFSR)

                print("\n*************************************** ")

        except IndexError:

            print("Error, seed of length", len(initString), "too short, must be length 20 or longer")

        self.initialize();
        self.second_taps = self.setTaps()
        self.second_taps = listToTaps(self.second_taps)
        self.FINAL_LFSR = LFSR(self.initialize(), self.second_taps)

        print("FINAL REGISTER DATA")

        self.FINAL_LFSR.printregister()
        self.FINAL_LFSR.printtaps()

    # ticks the horizontal registers and outputs a length-ten sequence
    def tap_tick(self):

        newTaps = [0,0,0,0,0,0,0,0,0,0]

        # cascading clock
        for i in range(0, 5, 1):

            newTaps[i] = self.machines[i].tick()
            if newTaps[i] == 1: newTaps[i+5] = self.machines[i+5].tick()
            
        zeros = 0
        ones = 0

        for i in range(10):

            if newTaps[i] == 0: zeros += 1
            if newTaps[i] == 1: ones += 1

        if zeros > ones: return (newTaps, 0)
        if zeros <= ones: return (newTaps, 1)

        
    # sets the vertical register's initial fill
    def initialize(self):

        output = list();

        for machine in self.machines:

            output.append(machine.tick())

        print (output)
        return output

    # sets the taps for the horizontal registers
    def setTaps(self):

        output = list()

        for machine in self.machines:

            output.append(machine.tick())

        return output

    # produces an output sequence
    def putout(self, number):

        output = list()

        for i in range(number):

            signal = self.tap_tick()

            #tick, new taps, tick, new taps
            output.append(self.FINAL_LFSR.tick() | signal[1])

            if(i%10 == 0):

                self.FINAL_LFSR.newtaps(listToTaps(signal[0]))
                #self.FINAL_LFSR.newregister(listToTaps(signal[0]))

        return output


# turns a character string into a binary string
def getSeed(seed):

    output = ''

    for i in range(len(seed)):

        interim = bin(ord(seed[i]))

        for j in range (2, len(interim)):

            output += interim[j]

    return output


# turns the binary string into a list for processing
def stringToList(seed):

    output = []

    for i in range(len(seed)):

        output.append(int(seed[i]))

    return output


# converts that list to taps in accordance with implementation
def listToTaps(inputList):

    polynomial = []

    for i in range(len(inputList)):

        if inputList[i] == 1:

            polynomial.insert(0,i+2)

    return polynomial
