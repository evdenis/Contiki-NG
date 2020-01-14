<img src="https://github.com/contiki-ng/contiki-ng.github.io/blob/master/images/logo/Contiki_logo_2RGB.png" alt="Logo" width="256">

# Contiki-NG: The OS for Next Generation IoT Devices

# Continuous Verification Framework for Contiki-NG

[![Verification Status](https://travis-ci.org/evdenis/Contiki-NG.svg?branch=develop)](https://travis-ci.org/evdenis/Contiki-NG)

The continious verification framework is designed as part of the CI system and configured to (try to) reprove all previously verified functions in the set of files modified by a code update (generally
submitted as a merge request). It relies on Travis-CI. It allows developers to constantly verify the evolving code and to detect potential inconsistencies early.

A timeout per verification condition is currently set between 10 and 20 seconds (depending on the function) to provide a fast feedback and to fit the global 50-minute time
limit of Travis-CI. This strict time limitation in the current demonstration version explains why the verification results for some provable properties can sometimes
appear as partially unsuccessful for lack of time: in this case, the timeout for such properties can be increased.
Coq proofs are currently not replayed because the Coq installation takes too long.

* The [list of verified functions](verif/contiki_status.conf) to replay
* The [verification status](verif/verdicts.txt) to compare against
* Coccinelle [patches](verif/patches)
* Frama-C [configuration](verif/contiki_extricate.conf) for different functions
* Travis-CI [configuration](.travis.yml)

[![Build Status](https://travis-ci.org/contiki-ng/contiki-ng.svg?branch=master)](https://travis-ci.org/contiki-ng/contiki-ng/branches)
[![license](https://img.shields.io/badge/license-3--clause%20bsd-brightgreen.svg)](https://github.com/contiki-ng/contiki-ng/blob/master/LICENSE.md)
[![Latest release](https://img.shields.io/github/release/contiki-ng/contiki-ng.svg)](https://github.com/contiki-ng/contiki-ng/releases/latest)
[![GitHub Release Date](https://img.shields.io/github/release-date/contiki-ng/contiki-ng.svg)](https://github.com/contiki-ng/contiki-ng/releases/latest)
[![Last commit](https://img.shields.io/github/last-commit/contiki-ng/contiki-ng.svg)](https://github.com/contiki-ng/contiki-ng/commit/HEAD)

# Overview of Contiki-NG 

Contiki-NG is an open-source, cross-platform operating system for Next-Generation IoT devices. It focuses on dependable (secure and reliable) low-power communication and standard protocols, such as IPv6/6LoWPAN, 6TiSCH, RPL, and CoAP. Contiki-NG comes with extensive documentation, tutorials, a roadmap, release cycle, and well-defined development flow for smooth integration of community contributions.

Unless explicitly stated otherwise, Contiki-NG sources are distributed under
the terms of the [3-clause BSD license](LICENSE.md). This license gives
everyone the right to use and distribute the code, either in binary or
source code format, as long as the copyright license is retained in
the source code.

Contiki-NG started as a fork of the Contiki OS and retains some of its original features.

Find out more:

* GitHub repository: https://github.com/contiki-ng/contiki-ng
* Documentation: https://github.com/contiki-ng/contiki-ng/wiki
* Web site: http://contiki-ng.org

Engage with the community:

* Gitter: https://gitter.im/contiki-ng
* Twitter: https://twitter.com/contiki_ng
