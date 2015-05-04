#!/bin/bash

printf "\033c" && grep $1 -e ':' | grep -e '^ *| ' | sed -e 's/:.*/ *) eauto./g' | sed -e 's/ *| /  + (* case /g'

