#!/usr/bin/env bash

herd7 $1 | grep -oE 'Ok|No'
