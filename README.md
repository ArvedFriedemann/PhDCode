# Code for the PhD "Towards a General Theory of Solving for Dependent Type Theory"

Thank you for reviewing my code for the thesis! 

The Agda code is fully self-contained. It can be compiled using the command 

```sh
agda OwnPrelude/Everything.agda
```

The ```Everything.agda``` file also contains an overview on which file contains the code for which chapter. 

The code has been compiled using:

Agda version 2.7.0
agda-stdlib v2.1-rc1
cubical v0.7


To compile all the files in the code, load the file ./Code/OwnPrelude/Everything.agda
This loads all modules relevant to this thesis. The file also contains an overview of which files relate to which chapter. If you cannot find a piece of code you are looking for, you can check the Code-Tags given in the thesis and search for them by simple string search.

Most of the code related to the thesis is in the ./Code/OwnPrelude/ folder.  The ./Code/Preliminaries/ folder contains the code for the preliminaries. In the ./Code/ASCIIPrelude/ you can find the ASCII names for functions in the standard library, as well as some proofs on basic data structures. I included my ASCIIPrelude directly in a folder of the same name, so the Agda code here should be self-contained without subrepositories. 

All modules are either marked --safe or have the flag commented out due to the postulate of the semilattice preorder being an indexed monoid (only postulate in the entire thesis and irrelevant to most results)

If you have any questions, feel free to contact me directly.
