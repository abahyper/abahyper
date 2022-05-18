# AbaHyper: Automata-based Model Checking of HyperLTL

This repository contains AbaHyper (short for **A**utomata-**ba**sed Model Checking of **Hyper**LTL), a tool that can model check HyperLTL properties on finite-state systems. 
AbaHyper reads a (finite-state) transition system, the hyperproperty to be checked and determines if the property holds on the given system.
Alternatively, the system can also be given as a boolean program which is compiled to a transition system. 

## Structure 

- `src/` contains the source code of AbaHyper written in F#.
- `examples/` contains a selection of examples.
- `app/` is the target folder for the build. It contains a `config.conf` file that should point to a local installation of *spot*, *BAIT* and *RABIT* (see Section [Build AbaHyper](#build-abahyper)).

## Build

To build and run AbaHyper you need the following

- [.NET 6 SDK](https://dotnet.microsoft.com/en-us/download) (tested with version 6.0.300)
- [JAVA JRE](https://www.java.com/de/) (tested with oracle-jdk version 18.0.1.1)
- [spot](https://spot.lrde.epita.fr/) (tested with version 2.10.4)
- [RABIT](https://github.com/iscas-tis/RABIT) (tested with version 2.4.5)
- [BAIT](https://github.com/parof/bait) (tested with version 0.1)


Begin by installing the .NET 6 SDK and a Java JRE (or JDK). 
Both the `dotnet` and `java` commands should be located in the path (test this by, e.g., running `dotnet --version` and `java --version`).
Java is used by AbaHyper to run the `.jar`s from *RABIT* and *BAIT*.
Details on the installation of *spot*, *RABIT* and *BAIT* are given below. 

### Build AbaHyper
To build AbaHyper run the following (when in the main directory of this repository).

```shell
cd src
dotnet build -c "release" -o ../app
cd ..
```

Afterwards, the AbaHyper executable is located in the `app/` folder.
Note that the AbaHyper executable is not standalone and requires the other files located in the `app/` folder.
In particular, to copy the executable, you need to copy the entire contents of the `app/` folder.


### Build and Connect spot, rabit and bait 

AbaHyper uses a suite of external solvers to delegate tasks such as automata complementations and language inclusion checks. 
It needs access to *spot* (more specifically, the `autfilt` and `ltl2tgba` command-line-tools of the *spot* library), *BAIT* and *RABIT*.
AbaHyper is designed such that it only needs the *absolute path* to each of the solvers listed above.
In particular, the user can install them at whatever location fits them best.

- **spot:** You can either build *spot* yourself or download a prebuilt binary for your architecture (see [here](https://spot.lrde.epita.fr/install.html)). All *spot* tools (including `autfilt` and `ltl2tgba`) should be located in the same directory.
- **RABIT:** Download *RABIT* from [here](https://github.com/iscas-tis/RABIT). This already includes the `RABIT.jar` that is required later.  
- **BAIT:** To install *BAIT* follow the instructions given [here](https://github.com/parof/bait). After building, locate the `bait.jar` file (which can be found in the `/build/libs/` folder).


After you have downloaded (and built) the above tools, you need to make them accessible to AbaHyper, by copying the **absolute** paths to each tool into a configuration file called `config.conf`.
The `config.conf` file **must** be located in the same directory as the AbaHyper executable (this convention makes it easy to find the config file, independent of the relative path AbaHyper is called from).
We already provide a config file `app/config.conf`.

For *spot* you need to copy the path to the *folder* where the *spot* tools are contained in. 
For *RABIT* and *BAIT* you need to copy the path to the `.jar` file of each tool.

For example, assume that *spot* installed in `/usr/local/bin` (so the executables `/usr/local/bin/autfilt` and `/usr/local/bin/ltl2tgba` exist), the *RABIT* Jar is located at `/home/user/RABIT.jar`, and the *BAIT* `.jar` is located at `/home/user/bait.jar`.
The content of `config.conf` should be the following:

```
[paths]
spot="/usr/local/bin"
rabit="/home/user/RABIT.jar"
bait="/home/user/bait.jar"
```

If *spot* is contained in the path, (check this by, e.g., running `autfilt --version`), you can simply set `spot=""`. 


## Run AbaHyper

After having built AbaHyper and set the path to the external solvers, you are ready to use AbaHyper.
There are two modes available. 
You can either model check a property on a file that contains an explicit transition system, or model check a property on a boolean program that is translated into a transition system by AbaHyper.

For the former run

```shell
./app/AbaHyper -prop propfile -ts tsfile
```

where `propfile` is the (path to the) file containing the HyperLTL property and `tsfile` the (path to the) file containing the transition system (see Section [Input for AbaHyper](#input-for-abahyper) for details).


For the latter run

```shell
./app/AbaHyper -prop propfile -prog progfile
```

where `propfile` is the (path to the) file containing the HyperLTL property and `progfile` the (path to the) file containing the boolean program (see Section [Input for AbaHyper](#input-for-abahyper) for details).

There also exists a mode run experiments coded in F#. See Section [Run Experiments](#run-experiments) for details.


### Examples

As a first example to verify a property on an explicit transition system run 

```shell
./app/AbaHyper -prop examples/explicit/prop1 -ts examples/explicit/ts1
```

As an example to verify a property on a program run 

```shell
./app/AbaHyper -prop examples/programs/gni -prog examples/programs/p1
```


## Input for AbaHyper

### Command-line Arguments

AbaHyper supports several command-line options.

- `-prop` sets the path to the file containing the HyperLTL property that needs to be checked. This option is mandatory.
- `-ts` sets the path to the transition system that should be verified. Exactly one of `-ts` or `-prog` (see below) needs to be set.
- `-prog` sets the path to the boolean program that should be verified. Exactly one of `-ts` or `-prog` needs to be set.
- `-m` sets the solver that should be used by AbaHyper. Supported options are `comp` (to use complementation and emptiness checks), `incl_spot` (to use the inclusion check of spot), `incl_bait` (to use the inclusion check of BAIT), and `incl_rabit` (to use the inclusion check of RABIT). This option is optional. If not used, the default option is `comp`.
- `-t` sets the timeout in seconds to be used. This option is optional. If not used, no timeout is used. 



### Specifying Transition System

Consider the following example transition system

```
init 0 1
aps "x" "y"
--BODY-- 
State: 0 [f f]
0 1 2 3
State: 1 [f t]
0 1 2 3
State: 2 [t f]
0 1 2 3
State: 3 [t t]
0 1 2 3
```

This specification declares states `0` and  `1` as initial states.
The APs are `x` and `y` which are given as *escaped* strings.
For each state, we give the evaluation of the atomic propositions as a list of booleans (either `f`, or `t`), which has the same length as the number of APs.
For example in state 1, `x` does not hold but `y` does.
Each state lists all successors of that node. 


A possible HyperLTL property can be specified as follows

```
forall exists (X (G ((X "x"_0 <-> "x"_1)))) 
```

We start with the quantifier prefix and follow with an LTL formula (in the format supported by *spot*).
The atomic propositions have the form `a_i` where `a` is the AP (this must, again, be escaped) and the index `i` refers to the trace variable (starting with 0).


### Specifying Boolean Programs

Consider the following example boolean program

```
dom: [(h 1), (l 1), (o 1)]
[
    o := (x t 1);
    WHILE(t) {
        [
            READ(h);
            IF((#h 0)) THEN {
                o := (! o)
            } ELSE {
                o := (& (!o) (| h (!h)))
            }
        ]
    }
]
```

Here the first line gives the bitwidth of each variable. 
A variable name is any sequence consisting only of *letters*.

When running, the value of each variable is a vector of boolean values.
We support the following language constructs.

Expressions have the form 
- A variable 
- `t` (true) or `f` (false)
- (Pointwise) conjunction or disjunction of two expressions with the same bitwidth `(& e1 e2)`, `(| e1 e2)`
- (Pointwise) negation `(! e)`
- Duplication, e.g., `(x e 5)` duplicates `e` 5 times (i.e., the value is a boolean list that has 5 times the length of the value of `e`)
- Projection: `(#e i)` where `i` is a natural number.

Statements have the form 
- Assignments: `x := e` where `e` is an expression and `x` a variable
- Inputs: `READ(x)` where `x` is a variable
- Conditionals: `IF(e) THEN { P1} ELSE {P2}` where `P1`, `P2` are statements and `e` is an expression
- Composition: `[P1; P2; ....; Pn]` where `P1`, ..., `Pn` are statements
- Loops: `WHILE(e) {P}` where `P` is a statement and `e` is an expression
- Nondeterministic branching: `NONDET THEN {P1} ELSE {P2}` where `P1`, `P2` are statements


A possible HyperLTL property can be specified as follows (we take GNI as an example)

```
forall forall exists (G ({h_0}_0 <-> {h_0}_2)) & (G({l_0}_1 <-> {l_0}_2)) & (G({o_0}_1 <-> {o_0}_2))
```

The atomic propositions have the form `{x_j}_i` where `x` is a variable in the program, `j` an index in the boolean vector value of `x` and the index `i` refers to the trace variable (starting with 0).
For example `{h_0}_0` refers to the first position in the boolean vector value of `h` on the first trace. 



## Run Experiments 

Apart from running AbaHyper on transitions systems (and/or programs), you can also use the codebase of AbaHyper to run experiments that produce plots. 
Existing plotting experiments are in the `src/PlotGenerator.fs` file and listed at the bottom of this file.
Each experiment consists of a name and the code to run on this experiment.
To add custom experiments simply add them to this list **and** rebuild AbaHyper (see [Build AbaHyper](#build-abahyper)). 
We recommend taking a look at the existing experiments in `src/PlotGenerator.fs`.

To run an experiment run 

```shell
./app/AbaHyper -e name
```

where `name` is the name of the experiment (as given in the list at the bottom of `src/PlotGenerator.fs`).
This will run the code (which will produce the desired `plotly` plot).
Existing experiments are named: `successSystemSize`, `survivalSystemSize`, `successAndMedianTimeSystemSize`, `survivalAlternation`, `complementationCostAlternation`, `successAndPositiveRate`, `ABVandSBVTimeSystem`, `ABVandSBVTimeProperty`, and `ABVandSBVTimeDensity`.