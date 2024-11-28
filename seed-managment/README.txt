BACKGROUND AND PURPOSE

A while back, u/brianddk (Reddit) put together a Python script for deriving the 25-word Monero mnemonic from a BIP39 Trezor-T seed phrase. Another tool, also in Python, does similar work, but it is outdated and has dependency issues, so I appreciate u/brianddk for getting it cleaned up and usable. Having a way to get your Monero seed from a Trezor seed is important in case you lose access to your Trezor-T (stolen, broken, lost, seized, etc.). The tool allows you to access your funds using any Monero wallet even if all Trezor devices were to vanish tomorrow.

One of the most powerful tools for safely backing up your cryptocurrency is the Shamir Secret Sharing protocol. It's flexible, secure, and can mitigate concerns of losing your seed phrase. Trezor has this option by default, but again, you cannot use these backup phrases to access your Monero without a physical Trezor.

I took the work u/brianddk did and combined it with Trezor's own Shamir recovery code to make a single, small Python script for accessing your Monero seed from either a "Standard" Trezor phrase or an "Advanced" Shamir Trezor phrase. I also made it an interactive CLI, so there's no need to edit the script and hardcode your mnemonic (not that this would be a big deal). The interactive CLI will also prompt you for your seed passphrase, if you use one. 

----------

TO INSTALL AND RUN

pip3 install --upgrade pip setuptools wheel
pip3 install click==8.1.3 trezor==0.13.7 monero==1.1.1 ecdsa==0.18.0 ed25519==1.5 shamir_mnemonic==0.3.0

### Run to interactively recover Monero seed phrase
python3 trezor-xmr-recovery.py

Note:
Consider compiling the Python to an executable using something like python3 -m PyInstaller --onefile --collect-all shamir_mnemonic trezor-xmr-recovery.py. Then you can keep a flash drive with the executable with your seed phrase or Shamir secrets. For convenience, I have released a pre-compiled binary, but you should not trust binaries from strangers with something as sensitive as your seed. If you use my binary, at least use it on an offline computer.
