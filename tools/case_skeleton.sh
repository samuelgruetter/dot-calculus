#!/bin/bash

printf "\033c" && grep $1 -e '^  | ' | sed -e 's/ :.*/ *)>    admit./g' | sed -e 's/  | /  + (* case /g' | tr '>' '\n'

