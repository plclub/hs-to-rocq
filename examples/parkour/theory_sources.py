"""Locate Parkour proof sources independently of their logical Rocq names."""

from collections.abc import Iterator
from pathlib import Path

_ROOT = Path(__file__).resolve().parent / "theories"

# Within each directory, an entry is LogicalSuffix[:PhysicalStem].
# A leading '=' denotes a module without the usual Deadlock prefix.
_GROUPS = {
    "contracts": """
        =Behavior =Integration =OwnerCond =ReaderTree =Required
        Contract Freedom MutationCases RepairCases
    """,
    "source": """
        Source SourceCases:Cases SourceExpect:Expect SourceExtraExpect:ExtraExpect
        SourceView:View WellFormed Roster Projection ProjectionExpect:EndpointExpect
    """,
    "execution": """
        Local Network NetworkCases:Cases Runs State StepView Enabled ReadyInputs
        Messages Quorum
    """,
    "history": """
        Chronology WireChronology Order Past ObservedCut CutSafety FirstSend SameHistory
    """,
    "layout": """
        AtomicLayout BranchLayout ChoiceLayout StructuralLayout LayoutHead:Head
        LayoutOrder:Order StaticPaths StaticBarrier:Barrier SubtreeBarrier
    """,
    "frontiers": """
        Alignment AlignmentProgress:Progress Coverage FrontierCoverage
        FrontierProofs:Proofs Frontiers:Boundaries Coherence
    """,
    "heads": """
        Head ChoiceHead PrefixHead RootHead StaticHead SelectedBody
    """,
    "origins": """
        AllOrigins ChoiceOrigin DynamicOrigin EnteredOrigin FamilyOrigin PureBindOrigin
        RootOrigin StaticOrigin
    """,
    "logs": """
        LocalLog LogAtoms:Atoms LogChoice:Choice LogDecompose:Decompose LogScope:Scope
        FamilyBranches:Branches FamilyChoice FamilyLog:Log
    """,
    "replay": """
        Replay Realized Match MatchStep:Step PayloadLedger PartialValues
        PlayedActual:Actual PlayedFamily:Family PlayedPrefix:Prefix PlayedValues:Values
    """,
}


def _source_paths() -> Iterator[tuple[str, Path]]:
    for directory, entries in _GROUPS.items():
        for entry in entries.split():
            suffix, _, stem = entry.partition(":")
            logical = suffix[1:] if suffix.startswith("=") else "Deadlock" + suffix
            yield logical, _ROOT / directory / ((stem or suffix.lstrip("=")) + ".v")


_SOURCES = dict(_source_paths())


def theory_source(name: str) -> Path:
    """Return the absolute source path for a legacy module stem (KeyError if unknown)."""
    return _SOURCES[name]
