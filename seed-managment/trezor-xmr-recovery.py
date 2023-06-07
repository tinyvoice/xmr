#!/usr/bin/env python3
# [rights]  Copyright 2023 tinyvoice at github https://github.com/tinyvoice
# [license] Apache 2.0 License https://www.apache.org/licenses/LICENSE-2.0
# [repo]    https://github.com/tinyvoice/xmr/blob/main/seed-managment/trezor-xmr-recovery.py
# [tipjar]  https://github.com/tinyvoice/xmr/blob/main/tipjar.txt
# [ref]     https://www.reddit.com/r/Monero/comments/1433ymb
# [req]     pip install click==8.1.3 trezor==0.13.7 monero==1.1.1 ecdsa==0.18.0 ed25519==1.5 shamir_mnemonic==0.2.2
# [note]    This script is for emergancy recovery of Monero funds from a
# [note]    Trezor-T hardware wallet using a Standard mnemonic or Shamir (Trezor Advanced) mnemonic shares.

## INSTALL AND RUN ##
#
# sudo apt install python3.10-venv
# python3 -m venv xmr.venv
# xmr.venv\Scripts\activate.bat  ### WINDOWS ONLY
# source xmr.venv/bin/activate ### LINUX AND MACOS ONLY
# pip3 install --upgrade pip setuptools wheel
# pip3 install click trezor monero ecdsa ed25519 shamir_mnemonic
# python3 trezor-xmr-recovery.py

## REFERENCES ##
#
# Credit for a large portion of the below code goes to https://github.com/brianddk
# - Added interactive CLI
# - Added Trezor Shamir recovery
# - Other minor fixes/cosmetic changes
#
# See https://github.com/satoshilabs/slips/blob/e9e52e8/slip-0010.md
# See https://github.com/satoshilabs/slips/blob/e9e52e8/slip-0010/testvectors.py
# See https://github.com/satoshilabs/slips/blob/e9e52e8/slip-0014.md
# See https://github.com/satoshilabs/slips/blob/master/slip-0039.md
# See https://github.com/trezor/trezor-firmware/blob/fee0d70/tests/common.py#L37
# See https://github.com/trezor/trezor-firmware/blob/fee0d70/tests/device_tests/monero/test_getaddress.py#L33
# See https://github.com/trezor/trezor-firmware/blob/fee0d70/docs/misc/coins-bip44-paths.md
# See https://github.com/trezor/python-shamir-mnemonic/tree/master/shamir_mnemonic

from typing import Sequence, Tuple
import click
from click import style
import binascii
import hashlib
import hmac
import struct
import ecdsa
import ed25519
from mnemonic import Mnemonic
from trezorlib.tools import parse_path
import monero.seed
import shamir_mnemonic
from shamir_mnemonic import cli
from shamir_mnemonic.recovery import RecoveryState
from shamir_mnemonic.shamir import generate_mnemonics
from shamir_mnemonic.share import Share
from shamir_mnemonic.utils import MnemonicError


VERSION=0.3
privdev = 0x80000000

FINISHED = style("\u2713", fg="green", bold=True)
EMPTY = style("\u2717", fg="red", bold=True)
INPROGRESS = style("\u25cf", fg="yellow", bold=True)


def error(s: str) -> None:
    click.echo(style("ERROR: ", fg="red") + s)
            
def recover_shamir(passphrase_prompt: bool, start_mnemonic_str) -> None:

    def add_share(mnemonic_str: str):
        try:
            share = Share.from_mnemonic(mnemonic_str)
            if not recovery_state.matches(share):
                error("This mnemonic is not part of the current set. Please try again.")
                return
            if share in recovery_state:
                error("Share already entered.")
                return

            recovery_state.add_share(share)
            print_status()

        except click.Abort:
            return
        except Exception as e:
            error(str(e))

    def print_group_status(idx: int) -> None:
        group_size, group_threshold = recovery_state.group_status(idx)
        group_prefix = style(recovery_state.group_prefix(idx), bold=True)
        bi = style(str(group_size), bold=True)
        if not group_size:
            click.echo(f"{EMPTY} {bi} shares from group {group_prefix}")
        else:
            prefix = FINISHED if group_size >= group_threshold else INPROGRESS
            bt = style(str(group_threshold), bold=True)
            click.echo(f"{prefix} {bi} of {bt} shares needed from group {group_prefix}")

    def print_status() -> None:
        bn = style(str(recovery_state.groups_complete()), bold=True)
        bt = style(str(recovery_state.parameters.group_threshold), bold=True)
        click.echo()
        if recovery_state.parameters.group_count > 1:
            click.echo(f"Completed {bn} of {bt} groups needed:")
        for i in range(recovery_state.parameters.group_count):
            print_group_status(i)
    
    
    
    recovery_state = RecoveryState()
    add_share(start_mnemonic_str)

    while not recovery_state.is_complete():
        add_share(click.prompt("\nEnter a recovery share"))

    passphrase_bytes = b""
    if passphrase_prompt:
        print()
        while True:
            passphrase = click.prompt(
                "Enter passphrase (leave blank if none)", hide_input=True, confirmation_prompt=False, default="", show_default=False
            )
            if not passphrase:
                break
            else:
                try:
                    passphrase_bytes = passphrase.encode("ascii")
                    break
                except UnicodeDecodeError:
                    click.echo("Passphrase must be ASCII. Please try again.")

    try:
        master_secret = recovery_state.recover(passphrase_bytes)
    except MnemonicError as e:
        error(str(e))
        click.echo("Recovery failed")
        sys.exit(1)
    click.secho("SUCCESS!", fg="green", bold=True)
    
    return master_secret.hex()

def int_to_string(x, pad):
    result = ['\x00'] * pad
    while x > 0:
        pad -= 1
        ordinal = x & 0xFF
        result[pad] = (chr(ordinal))
        x >>= 8
    return ''.join(result)


def string_to_int(s):
    result = 0
    for c in s:
        if not isinstance(c, int):
            c = ord(c)
        result = (result << 8) + c
    return result


# mode 0 - compatible with BIP32 private derivation
def seed2hdnode(seed, modifier, curve):
    k = seed
    while True:
        h = hmac.new(modifier.encode(), seed, hashlib.sha512).digest()
        key, chaincode = h[:32], h[32:]
        a = string_to_int(key)
        if (curve == 'ed25519'):
            break
        if (a < curve.order and a != 0):
            break
        seed = h
    return (key, chaincode)


def publickey(private_key, curve):
    if curve == 'ed25519':
        sk = ed25519.SigningKey(private_key)
        return b'\x00' + sk.get_verifying_key().to_bytes()
    else:
        Q = string_to_int(private_key) * curve.generator
        xstr = int_to_string(Q.x(), 32)
        parity = Q.y() & 1
        return chr(2 + parity) + xstr


def derive(parent_key, parent_chaincode, i, curve):
    assert len(parent_key) == 32
    assert len(parent_chaincode) == 32
    k = parent_chaincode
    if ((i & privdev) != 0):
        key = b'\x00' + parent_key
    else:
        key = publickey(parent_key, curve)
    d = key + struct.pack('>L', i)
    while True:
        h = hmac.new(k, d, hashlib.sha512).digest()
        key, chaincode = h[:32], h[32:]
        if curve == 'ed25519':
            break
        a = string_to_int(key)
        key = (a + string_to_int(parent_key)) % curve.order
        if (a < curve.order and key != 0):
            key = int_to_string(key, 32)
            break
        d = '\x01' + h[32:] + struct.pack('>L', i)                        
    return (key, chaincode)


def get_curve_info(curvename):
    if curvename == 'secp256k1':
        return (ecdsa.curves.SECP256k1, 'Bitcoin seed') 
    if curvename == 'nist256p1':
        return (ecdsa.curves.NIST256p, 'Nist256p1 seed') 
    if curvename == 'ed25519':
        return ('ed25519', 'ed25519 seed')
    raise BaseException('unsupported curve: '+curvename)


def get_keys(seedhex, derivationpath):
    curve, seedmodifier = get_curve_info('ed25519')
    master_seed = binascii.unhexlify(seedhex)
    k,c = seed2hdnode(master_seed, seedmodifier, curve)
    p = publickey(k, curve)
    depth = 0
    for i in derivationpath:
        i = i | privdev
        depth = depth + 1
        k,c = derive(k, c, i, curve)
        p = publickey(k, curve) 
    return p,k


def print_keys_from_mnemonic(derivation, mnemonic, passphrase = ""):
    bip39_seed = Mnemonic("english").to_seed(mnemonic, passphrase)
    pub, priv = get_keys(bip39_seed.hex(), parse_path(derivation))
    seed = monero.seed.Seed(priv.hex())
    pub_hex = '12' + seed.public_spend_key() + seed.public_view_key()
    chksum = monero.keccak.keccak_256(bytes.fromhex(pub_hex)).digest().hex()
    address = monero.base58.encode(pub_hex + chksum[:8])
    print_results(mnemonic, bip39_seed.hex(), derivation, priv, seed, address)
    return address

def print_keys_from_seed(derivation, bip39_seed):
    pub, priv = get_keys(bip39_seed, parse_path(derivation))
    seed = monero.seed.Seed(priv.hex())
    pub_hex = '12' + seed.public_spend_key() + seed.public_view_key()
    chksum = monero.keccak.keccak_256(bytes.fromhex(pub_hex)).digest().hex()
    address = monero.base58.encode(pub_hex + chksum[:8])
    print_results("N/A", bip39_seed, derivation, priv, seed, address)
    return address
    
def print_results(mnemonic, bip39_seed, derivation, priv, seed, address):
    print("----- RESULTS -----\n")
    print("BIP39 Mnemonic:", mnemonic)
    print("BIP39 Seed:", bip39_seed)
    print("SLIP10 Derivation:", derivation)
    print("SLIP10 Seed at Derivation:", priv.hex())
    print()
    group_str = (
    		style("Monero Mnemonic:\n")
		+ style(seed.phrase, bold=True, fg="bright_red")
		)
    print(group_str)
    print()
    print("Monero Address:", address)
    print("Monero Public Spend:", seed.public_spend_key())
    print("Monero Public View:", seed.public_view_key())
    print("Monero Private Spend:", seed.secret_spend_key())
    print("Monero Private View:", seed.secret_view_key())
    print("\n----- END RESULTS -----\n")
    

derivation = "m/44h/128h/0h"

print("\nTrezor to Monero Seed Converter")
print("Version: ", VERSION, "\n")
click.echo(style("WARNING: ", fg="red") + "ONLY run this program on an air-gapped (no internet connection) and secured computer. This program reads and uses your private key.\n")

while True:
    start_mnemonic = input("Enter your Trezor Standard backup phrase or a Shamir backup phrase: ")
    start_mnemonic = start_mnemonic.strip()
    mnemonic_words = start_mnemonic.split()

    if len(mnemonic_words) == 12 or len(mnemonic_words) == 18 or len(mnemonic_words) == 24:
    # Input phrase is a standard Trezor phrase
            your_passphrase = input("\nEnter passphrase (leave blank if none): ")
            print("\n")
            print_keys_from_mnemonic(derivation, start_mnemonic, your_passphrase)
            break
    elif len(mnemonic_words) == 20 or len(mnemonic_words) == 33:
    # Input phrase is a Trezor Shamir share
            seed = recover_shamir(True, start_mnemonic)
            print()
            print_keys_from_seed(derivation, seed)
            break
    else:
            click.echo(style("\n\nERROR: ", fg="red") + "Incorrect formatting or word count. Make sure there are no leading or trailing carriage returns. Please restart the program.\n")
            break
