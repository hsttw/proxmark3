# Unofficial proxmark3 repository.
### This is just a fork with slightly modifications for educational purposes only.

### What I did:
I've personally recoded the image of the ARM in order to automate
the attack and simulation on Mifare cards. I've moved some of the
implementation on the client side to the ARM such as *chk*, *ecfill*, *sim*
and *clone* commands. 

### What it does now:
It will check if the keys from the attacked tag are a subset from
the hardcoded set of keys inside of the FPGA. If this is the case
then it will load the keys into the emulator memory and also the
content of the victim tag, to finally simulate it and make a clone
on a blank card.

#### TODO:
- Nested attack in the case not all keys are known.
- Dump into magic card in case of needed replication.

#### ~ Basically automates commands without user intervention.
#### ~ No need of interface.
#### ~ Just a portable battery or an OTG usb cable for power supply.

## Spanish full description of the project [here](http://bit.ly/2c9nZXR).

For more information about the proxmark3 project don't hesitate to check [their repository](https://github.com/Proxmark/proxmark3).
