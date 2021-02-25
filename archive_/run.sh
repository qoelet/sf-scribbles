#!/usr/bin/env bash

find lf/ | entr -cdp coqc -verbose lf/*.v
