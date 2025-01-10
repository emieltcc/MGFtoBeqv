# MGFtoBeqv package

This repository contains the MGFtoBeqv package for Mathematica.

The MGFtoBeqv package facilitates the translation from MGFs in their lattice-sum representation to their modular iterated integral representation.

The functions defined in the MGFtoBeqv package are derived from the paper [1].

1. E. Claasen and M. Doroudiani, From Modular Graph Forms to Modular Iterated Integrals, arXiv:hep-th/2025.abcde.

## Getting Started

To get started clone this repository to your local machine.

```
git clone https://github.com/emieltcc/MGFtoBeqv.git mgftobeqv
```

Alternatively, you can download the contents of this repository by clicking on **Code** and then **Download Zip** in the top right corner.
The MGFtoBeqv package needs an additional package with .txt files, which can be downloaded from the internet using by first going to the newly created folder

```
cd mgftobeqv
```
after which we can download the files using

```
curl -O "https://arxiv.org/src/2007.05476v2/anc/{DiIds.txt,TriIds.txt,ModularGraphForms.m}"
```

Alternatively, you can go to https://arxiv.org/src/2007.05476v2/anc and download the files from there. These need to be put into the same folder as the package.

After cloning the repository open and run the Mathematica notebook **User_Manual.nb**. It contains a brief introduction to the MGFtoBeqv package and explains all the functions and symbols that the package provides.

## Usage

The MGFtoBeqv package consist of the package file ***MGFtoBevq.wl*** and two .txt files that store constants of the Laurent polynomials of depth 2 and 3 modular iterated integrals.

To load the package into a Mathematica notebook write:

```
Get["MGFtoBeqv.wl"]
```

## License
Copyright © 2025 Emiel Claasen

The MGFtoBeqv Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.
The MGFtoBeqv Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.
