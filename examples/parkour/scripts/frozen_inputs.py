"""Verify the reviewed Parkour inputs used by the independent proof contracts."""

import hashlib
import subprocess
from pathlib import Path

from itree_pins import PARKOUR

LOCAL = {
    "deadlock-local-v1.sha256": "26cf0649672d228a135bd086088ac17727678e17585afe3281b81dbe303e6826",
    "deadlock-local-exact.sha256": "dca7c40a980377b7726e2bcc1c95ef8ef19d1d8e46d61a65795d772799d1ac60",
}
MANIFESTS = {
    **LOCAL,
    "DeadlockConcreteContract.sha256": "8996f8d5c8167285255418f402fadddccf50ae0f82e44ab913bbbec1a072977d",
    "DeadlockSourceOccurrenceExpect.sha256": "d2231dd81efc5f5f06ef43ce596f98f637220adc9a247e51c7aaf2d63e64dcff",
    "DeadlockSourceOccurrenceAmendment.sha256": "9971b74303f3e5e9937067d3a2358e487174396cc8318db603516991ea5a6dd9",
    "DeadlockProjectionExpect.sha256": "06588db992d1e953fcc2fc578b7ca5edf496e1a28ce465cdf171fb5a164c96ae",
    "DeadlockLibraryExpect.sha256": "c91b31607d06c104e763fe3feb574bca467911b2ebd4b1a4981c721f44d68b66",
    "DeadlockMutationExpect.sha256": "2dfd6665bfa0a76917c3a7c409c5c95aa13ff1810ffc48ae684c68e08773e3de",
    "DeadlockRunsExpect.sha256": "9874357e3c0422a9192628130303e1000cd0fa30e7f8639d21e1af3ae5526ad7",
    "deadlock-source-ordering-v2.sha256": "f11384df42257135cff135685de88bda7b53dbdbe2af780fda2383feb1398c9a",
    "deadlock-source-extra-v1.sha256": "e2c4a5922bf748964f8ec6575ca30a4a8ccb6b86c3ea731679f211dbb168a128",
    "DeadlockOrderExpect.sha256": "37162926b6b33b04eb1c3fee0edde9a1d3f93870d67f4935bdcf704fd4ad913c",
    "DeadlockWellFormedExpect.sha256": "2fb66452ddf3189e8ba70c5d553d3f04d630238b1a86f4fcee52a1ca3e28a5f2",
    "DeadlockWellFormedPartialExpect.sha256": "4f8922b22f3403d58383714569d5cb878063ff3df7e65c9f589e43d3fc7acfb6",
    "deadlock-network.sha256": "1f552cc30287fd1ae364039ff3d65f0dad329dde1484d626cda78be059a506d4",
    "deadlock-network-expect-v1.sha256": "1414d09949cc46ff4e8a5bd9b4a64b48bf80cf1fa9784e43814a987443fcbbf4",
    "deadlock-network-more-v1.sha256": "4c33d108db7b7f771a662a70e55172b017e9169925a5094f596c1f96f740c1cd",
    "deadlock-network-silent-v1.sha256": "f0199afa57d067ecba09418b9d50b8def0f3b15991bf7372fba430f8961a8bfa",
    "DeadlockQuorumExpect.sha256": "2c2099a22e44e6231bddb7a214b05b965dad8b5e7e0286a82fffc7c8631ec6ec",
}

# These expectations and concrete positive/negative runs had direct SHA-256
# anchors before the namespace migration, separately from the manifests above.
DIRECT = [
    "405818a74c3f68f1c3e2e0e015482a5d41f1edd0e81db2f2fc1b8b54f52d98dc",  # RoleStoreContract
    "39702217b967299a2c40eed0252acc6f0019b28b7a2acebcf1e352ddf06e378f",  # EnablednessContracts
    "fbc4c4f8c71f830d29c1924344f0d3cc19ca4adb6b4f4dfdc534329db7b2266a",  # QueueRepresentation
    "7ae72daa2a26b15539226f7c86c4432961f40d0a4e33329a791bc8f88b53ec37",  # PrefixRelationContracts
    "b845b79ebb8939b5c622cb5a750a401f94eb2321235eba8ed08d5ca00c21c0e2",  # PrefixExtensionContracts
    "a672d0bf4470181fbc4b0be869e0da74dc4404839b309b0c89c0b20010a0a1d5",  # ChoicePayloadMatching
    "9658a221b45bc64ffd29254eb5f543b54b40256da13e66cd53ccd8937d92d204",  # ParallelAndChoiceMatches
    "4b37bb9b4a72a247d55ce94043052c86919f0300566db1d23176058d3ea7b9cf",  # ScheduledTraceContracts
    "846ed227b5a0e515fff2e044535ee8dc235f602ee4de2e713991edb0d91b51e5",  # WrongAnnouncementValue
    "c2b6f45e2fb69edf5ef828bff82834dc69379d86835ca3660c2fe4c453b3b627",  # ScheduledTraceWitnesses
]


def checked(path: Path, expected: str) -> bytes:
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise SystemExit(f"changed frozen input: {path}")
    return data


def verify(root: Path, generated: Path, *, local: bool) -> None:
    # One historical input may now live in more than one module. Check each
    # part, including the library definitions used by an independent fixture.
    table = checked(PARKOUR / "tests/namespace-migration.tsv", "dfa5b91c676d956f32351a92b512e017bd1f9e4db1519075fdaefd2cd622a5af")
    relocated: dict[str, list[tuple[str, str]]] = {}
    for row in table.decode().splitlines():
        old, new, path = row.split("\t")
        relocated.setdefault(old, []).append((new, path))
    needed = set[str]()
    for name, anchor in (LOCAL if local else MANIFESTS).items():
        for row in checked(PARKOUR / "tests" / name, anchor).decode().splitlines():
            expected, filename = row.split("  ", 1)
            relative = filename.removeprefix("examples/parkour/")
            if relative.startswith("lib/"):
                checked(generated / relative.removeprefix("lib/"), expected)
            elif expected == "eec7c4d4b62cac0713521a83613ba5318940d7260cc7508ba21004346fed7d9c":
                # The earlier source predates the occurrence-rule amendment.
                original = subprocess.check_output(
                    ["git", "cat-file", "blob", "d97eeb4607c670944977fe0417addbc2fb3464c3"], cwd=PARKOUR)
                if hashlib.sha256(original).hexdigest() != expected:
                    raise SystemExit("changed historical choreography semantics")
            elif relative.endswith(".v"):
                needed.add(expected)
            else:
                checked(PARKOUR / relative, expected)
    if not local:
        needed.update(DIRECT)
        if needed != relocated.keys():
            raise SystemExit("namespace migration does not account for every frozen source")
    for old in needed:
        for new, path in relocated[old]:
            checked(root / path, new)


def verify_local_inputs(project_root: Path) -> None:
    verify(project_root, project_root / "lib", local=True)


def verify_frozen_inputs(project_root: Path, generated: Path) -> None:
    verify(project_root, generated, local=False)
