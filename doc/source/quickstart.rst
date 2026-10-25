==========
Quickstart
==========

The easiest way to see how to use ``hs-to-rocq`` is to look at the Makefiles in
each of the subdirectories in the `examples <https://github.com/plclub/hs-to-rocq/tree/master/examples/>`_ subdirectory of the repository.

Translating a single Haskell file
---------------------------------

You can run `hs-to-rocq` on a single Haskell module (called `Main.hs`) with the
following command.

.. code-block:: shell

     $ stack exec -- hs-to-rocq -e hs-to-rocq/base/edits Main.hs --iface-dir hs-to-rocq/base -o .

Adjust the paths to the edits and base files in the ``hs-to-rocq`` repository accordingly. This invocation
uses the following commandline options.

.. option:: -e <editfile>

The ``-e`` command line argument tells ``hs-to-rocq`` to use edits from the
specified edit file, and can be used multiple times.
In almost every case, you'll want to include ``-e hs-to-rocq/base/edits``, the
edit file distributed with the base library.

.. option:: --iface-dir <dir>

The ``--iface-dir`` command line argument tells ``hs-to-rocq`` where to find
the interface files for the translated files in the ``base`` library. These
interface files contain extra information about produced during translation
and are needed to translate any modules that use the ``base`` libraries.


.. option:: -o <dir>

The ``-o`` argument specifies the output directory for the generated ``.v`` files.
In this case, it is the current directory.

.. option:: --target-version {8.20|9.0}

Selects the target Rocq/Coq version. The default is ``8.20``, which emits
``Coq.*`` qualified names and preserves the pre-Rocq-9 output. Passing
``--target-version 9.0`` rewrites standard-library references in generated
declarations for Rocq 9.0. For modules that now re-export definitions from Corelib,
the tool uses ``Corelib.*`` paths, including nested module paths. It uses
``Stdlib.*`` for other standard-library references. The tool also adjusts the
static header and names in user preambles and midambles.

The `simple <https://github.com/plclub/hs-to-rocq/tree/master/examples/simple>`_
example shows how to invoke ``hs-to-rocq`` from a ``Makefile``.

Building the Rocq 9.0 examples
-----------------------------

The ``examples/rocq9.0/`` tree provides the matching base library and reuses the
shared unit tests with ``rocq c``. After building ``hs-to-rocq``, use a Rocq 9.0
environment with Equations installed and run this command from the repository root:

.. code-block:: shell

     $ make -C examples/rocq9.0

The ``clean`` target deletes the convenience copy in ``examples/rocq9.0/base/``
as well as test outputs. To regenerate and rebuild it, initialize the GHC submodule
and run:

.. code-block:: shell

     $ git submodule update --init examples/ghc/ghc
     $ make -C examples/rocq9.0 clean
     $ make -j2 -C examples/rocq9.0

The build regenerates all base sources before creating the base Makefile and
compiling them. Running ``make -C examples/rocq9.0`` without ``-j2`` also
regenerates the missing sources; no separate ``vfiles`` step is needed.

Local Edit files
----------------

Often, a particular file will require its own set of edits. These edits can be
provided with additional uses of the ``-e <editfile>`` command line argument.

An example that uses a local edit file is `intervals <https://github.com/plclub/hs-to-rocq/tree/master/examples/intervals>`_,
as described in Joachim Breitner's
`blog post <https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it>`_.

Any number of edit files may be provided to ``hs-to-rocq``. 

Additional Coq definitions
--------------------------

Sometimes an ``hs-to-rocq`` translation requires the addition of Coq definitions to the output.
These definitions can be specified via the ``preamble`` and ``midamble``
arguments.

.. option:: -p <preamble-file>

Inserts the Coq definitions from the specified file at
the beginning of the output.

For example, the `rle
<https://github.com/plclub/hs-to-rocq/tree/master/examples/rle>`_ example uses
a preamble to add additional imports to the output.

.. option:: -m <midamble-file>

Inserts the Coq definitions from the specified file in the output after the
type definitions but before any of the translated code or instance
declarations.

Only one preamble and one midamble can be provided to ``hs-to-rocq``.

With ``--target-version 9.0``, the tool rewrites dotted ``Coq.*`` names in both
files, including the move from ``Coq.Program.Wf.WfExtensionality`` to
``Stdlib.Program.WfExtensionality.WfExtensionality``. The static header imports
``Stdlib.Program.WfExtensionality`` once before user definitions, so loading does
not depend on the spelling or spacing of a user ``Require`` command. The text
rewriter does not insert extra imports. It does not rewrite bare
``From Coq Require ...`` commands; use a dotted form such as
``From Coq.Program Require Import Wf.`` for text shared by both targets.
The Coq 8.20 target leaves preamble and midamble text unchanged.

Strict vs. permissive translation
---------------------------------

What should ``hs-to-rocq`` do when it can't translate a definition?  By default,
it will throw an error and stop translating.  But you can make this behavior
more permissive if you want.

.. option:: --strict
.. option:: -S

The default option: any definition that can't be translated will stop the whole
development process.

.. option:: --permissive
.. option:: -P

In permissive mode, ``hs-to-rocq`` will either attempt to axiomatize or skip
failing definitions when possible.  This is particularly useful during
development.

Proofs
------

Once you have translated your module with ``hs-to-rocq``, you will want to
prove stuff about it.  However, if your module includes definitions from
``base``, you need to set up a ``_CoqProject`` file so that ``coq`` can find
all of the necessary definitions.

The Makefile in the rle_ example demonstrates how this file can be constructed
automatically. The proofs in this example use a lemma called ``map_map`` from
the base library.

Translating a multi-file project
--------------------------------

Larger examples include
`containers
<https://github.com/plclub/hs-to-rocq/tree/master/examples/containers>`_  and
`transformers <https://github.com/plclub/hs-to-rocq/tree/master/examples/transformers>`_.

These examples use a ``Makefile`` to translate each module in the library
individually, using edit files, preambles and midambles specific to each
module. It also includes the addition of manually written Coq files to the
library.

For this scale of project, we recommend starting with one of the Makefiles
above and editing it to suit your application.

Avoiding ``base``
-----------------

``hs-to-rocq`` is designed to automatically use definitions from the ``base``
library. However, it is sometimes possible to translate small examples so that
they are self contained and only require definitions from Coq's standard
library.

An example project that takes this approach is:
https://github.com/mit-plv/riscv-coq


