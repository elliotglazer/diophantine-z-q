#!/bin/bash
# usage: scratch/gt-valence/mk.sh NAME  -- compiles scratch/gt-valence/VC/NAME.lean to an olean (module VC.NAME)
cd ~/dzq-wt/gt-valence
lake env bash -c "LEAN_PATH=\$LEAN_PATH:scratch/gt-valence/build lean -R scratch/gt-valence -o scratch/gt-valence/build/VC/$1.olean scratch/gt-valence/VC/$1.lean"
