// Copyright (c) 2017-2019 Khronos Group. This work is licensed under a
// Creative Commons Attribution 4.0 International License; see
// http://creativecommons.org/licenses/by/4.0/

// Vulkan + SPIR-V Memory Model

// Inspired by: Wickerson et al, Automatically Comparing Memory Consistency Models, POPL`17
// https://johnwickerson.github.io/papers/memalloy.pdf
// https://github.com/johnwickerson/memalloy

open util/relation

pred is_acyclic[r : E -> E] {
  acyclic[r, E]
}

pred strict_partial_order[r : E -> E] {
  is_acyclic[r]
  transitive[r]
}

pred is_equivalence[r : E -> E, s : set E] {
  equivalence[r,s]
  r in s->s
}

// stor = "set to relation", (s,s) for all s in E
// lift a set to a relation (the [_] operator in Herd)
fun stor[s : set E] : E -> E {
  s <: iden
}

// reduce a transitive relation to those immediately related
fun imm[r : E -> E] : E -> E{
  r - (r.^r)
}

// reflexive closure (the ?-operator in Herd)
fun rc[r : E -> E] : E -> E {
  r + (E <: iden)
}

// Relation-And-Inverse
fun rai[r : E -> E] : E -> E {
  r + ~r
}

// An "event" (instruction)
sig E {}

// An execution
sig Exec {
  EV : set E, // everything
  W, R, F : set E, // write, read, fence
  A, ACQ, REL: set E, // atomic, acquire, release
  SC0, SC1 : set E, // storage classes 0 and 1
  SEMSC0, SEMSC1, SEMSC01 : set E, // storage class semantics 0, 1, 0 and 1
  SCOPESG, SCOPEWG, SCOPEQF, SCOPEDEV : set E, // subgroup/workgroup/queuefamily/device scopes
  CBAR : set E, // control barrier
  RFINIT : set E, // reads that read-from the initial value
  AV, VIS : set E, // per-instruction availability/visibility operations
  AVSHADER, VISSHADER : set E, // availability/visibility op to shader domain
  AVQF, VISQF : set E, // availability/visibility op to queuefamily instance domain
  AVWG, VISWG : set E, // availability/visibility op to workgroup instance domain
  AVSG, VISSG : set E, // availability/visibility op to subgroup instance domain
  SEMAV, SEMVIS : set E, // memory semantics for availability/visibility operations
  AVDEVICE, VISDEVICE : set E, // availability/visibility op to device domain
  NONPRIV, PRIV : set E, // non-private (participates in inter-thread ordering) vs private

  // relations statically defined by a "program"
  sthd : E->E, // same thread
  immpo: E->E, // program order, only immediate neighbors
  pgmsloc : E->E, // same location specified in program source (see also sloc)
  ssg : E->E, // same subgroup
  swg : E->E, // same workgroup
  sqf : E->E, // same queuefamily
  ssw : E->E, // system-synchronizes-with
  scbarinst : E->E, // same control barrier dynamic instance
  pgmsref : E->E, // same reference specified in program source (see also sref)
  chains : E->E, // What availability/visibility chains are supported based on device state.
                 // chains is either EV->EV (if chains are supported) or stor[EV] (if not)

  // derived static relations
  po : E->E, // program order (^immpo)
  posctosem : E->E, // program order & (SC->SEM)
  posemtosc : E->E, // program order & (SEM->SC)
  inscope : E->E, // are a,b in each other's memory scope instance
  mutordatom : E->E, // mututally ordered atomics (same loc, inscope)
  sloc : E->E, // same location (roughly, transitive closure of pgmsloc)
  sref : E->E, // same reference (roughly, transitive closure of pgmsref + stor[R+W])
  avvisinc : E->E, // relates av/vis ops with those operations they may include

  // dynamic relations established at runtime
  rf : E->E, // reads-from
  asmo: E->E, // A's scoped modification order
  rs : E->E, // release sequence
  hypors : E->E, // hypothetical release sequence
  fr: E->E, // from-read
  sw: E->E, // synchronizes-with
  ithbsemsc0 : E->E, // inter-thread-happens-before (templated by storage class mask)
  ithbsemsc1 : E->E,
  ithbsemsc01 : E->E,
  hb: E->E, // happens-before
  avsg: E->E, // chain of instructions producing subgroup availability
  avwg: E->E, // chain of instructions producing workgroup availability
  avqf: E->E, // chain of instructions producing queue family availability
  avsh: E->E, // chain of instructions producing shader availability
  avdv: E->E, // device availability
  vissg: E->E, // chain of instructions producing subgroup visibility
  viswg: E->E, // chain of instructions producing workgroup visibility
  visqf: E->E, // chain of instructions producing queue family visibility
  vissh: E->E, // chain of instructions producing shader visibility
  visdv: E->E, // device visibility
  locord: E->E, // location-ordered
  dr: E->E, // data-race
  visto: E->E, // visible-to
} {

  // reads, writes, fences, barriers, and av/vis ops are the entire set of events
  R+W+F+CBAR+AVDEVICE+VISDEVICE = EV

  // memory accesses are disjoint from barriers
  // NOTE: Some CBARs are fences
  no ((R+W)&(F+CBAR))

  // program order is a subset of same-thread
  po in sthd

  // immpo is only "immediate" program order links, to reduce noise when visualizing
  // and to make it easier to specify. po is its transitive closure
  po = ^immpo

  // program order is a strict partial order
  strict_partial_order[po]
  // po relates everything in a thread
  (sthd - iden) = rai[po]

  // sthd is an equivalence relation
  is_equivalence[sthd, EV]

  // sloc is the transitive closure of all slocs specified in pgmsloc (and its
  // inverse) and add the identity over R+W
  sloc = ^(rai[pgmsloc]) + stor[R+W]
  // sloc is an equivalence relation over R+W
  is_equivalence[sloc, R+W]

  // sref is the transitive closure of all srefs specified in pgmsref (and its
  // inverse) and add the identity over R+W
  sref = ^(rai[pgmsref]) + stor[R+W]

  // Currently, all av/vis ops to device domain are assumed to include all references.
  // Semav/vis ops with SEMSCi apply to all ops in SCi, except themselves (e.g. atomic
  // write doesn't make itself available because the av op happens before the atomic write,
  // hence the "- iden").
  // AV+VIS ops (per-instruction) are avvisinc with themselves (av/vis op happens in the right order)
  // and with those operations on the same reference.
  // Note that this complexity exists in part because we don't split out implicit av/vis
  // ops as distinct instructions.
  avvisinc = (rai[((SC0+SC1)->(AVDEVICE+VISDEVICE)) +
                   (SC0->((SEMAV+SEMVIS)&SEMSC0)) +
                   (SC1->((SEMAV+SEMVIS)&SEMSC1))]) - iden +
              (rai[stor[AV+VIS] . (sref & sloc)])

  // same thread is a subset of same subgroup which is a subset of same workgroup
  sthd in ssg
  ssg in swg
  swg in sqf

  // same subgroup/workgroup/queuefamily are equivalence relationships
  is_equivalence[ssg, EV]
  is_equivalence[swg, EV]
  is_equivalence[sqf, EV]

  // reads-from maps writes to reads (that don't read-from init)
  // at the same location.
  rf in (W->(R-RFINIT)) & (sloc-iden)

  // reads-from is one-to-one
  rf . ~rf in iden

  // reads may read from the initial value
  RFINIT in R

  // All reads must read from some write or from init (the size of rf and
  // RFINIT must equal the size of R)
  #(rf + (stor[RFINIT])) = #R

  // RMW atomics in A
  (R&W) in A

  // Atomics are reads and writes, not fences
  A in R+W

  // acquire can be used on atomic reads or fences
  ACQ in ((R&A)+F)

  // releases can be used on atomic writes or fences
  REL in ((W&A)+F)

  // Fences must release or acquire
  F in (ACQ+REL)

  // Only writes/reads can have explicit availability/visibility ops, respectively
  AV in W
  VIS in R

  // nonpriv is only meaningful for memory accesses
  NONPRIV in R+W
  // PRIV is the complement of NONPRIV
  PRIV = R+W-NONPRIV

  // availability/visibility semantics in REL/ACQ only, respectively
  SEMAV in REL
  SEMVIS in ACQ

  // All coherent ops have implicit availability/visibility ops (AV, VIS).
  // Barriers/atomics can also include availability/visibility ops via their semantics (SEMAV, SEMVIS).
  AVSHADER = (AV+SEMAV) & SCOPEDEV
  VISSHADER = (VIS+SEMVIS) & SCOPEDEV

  AVQF = (AV+SEMAV) & (SCOPEDEV + SCOPEQF)
  VISQF = (VIS+SEMVIS) & (SCOPEDEV + SCOPEQF)

  AVWG = (AV+SEMAV) & (SCOPEDEV + SCOPEQF + SCOPEWG)
  VISWG = (VIS+SEMVIS) & (SCOPEDEV + SCOPEQF + SCOPEWG)

  AVSG = AV+SEMAV
  VISSG = VIS+SEMVIS

  // AV/VISDEVICE are not reads/writes, don't have storage classes, etc. They are
  // special operation invoked outside of a shader.
  no (R+W+F+CBAR+AV+VIS+RFINIT+ACQ+REL+SC0+SC1+SEMSC0+SEMSC1)&(AVDEVICE+VISDEVICE)
  no AVDEVICE&VISDEVICE

  // scbarinst relates pairs of control barriers
  is_equivalence[scbarinst, CBAR]
  // no pair of the same control barrier instance can be in the same thread
  no scbarinst & rai[po]
  // can't have two cbars where one comes first in po in one thread and
  // second in po in another thread
  no (po.scbarinst.po & scbarinst)
  // the same instance of a control barrier must have same scope, acq/rel, semantics
  no scbarinst & (SCOPEDEV -> (EV-SCOPEDEV))
  no scbarinst & (SCOPEQF -> (EV-SCOPEQF))
  no scbarinst & (SCOPEWG -> (EV-SCOPEWG))
  no scbarinst & (SCOPESG -> (EV-SCOPESG))
  no scbarinst & (ACQ -> (EV-ACQ))
  no scbarinst & (REL -> (EV-REL))
  no scbarinst & (SEMSC0 -> (EV-SEMSC0))
  no scbarinst & (SEMSC1 -> (EV-SEMSC1))

  // There is a unique storage class for each memory access.
  SC0+SC1 = R+W
  no SC0&SC1

  // All acquire/release ops have one or more semantics storage classes
  ACQ+REL = SEMSC0+SEMSC1
  SEMSC01 = SEMSC0&SEMSC1

  // All atomics and fences have a single scope
  A+F+CBAR in SCOPESG+SCOPEWG+SCOPEQF+SCOPEDEV
  no SCOPEQF&SCOPEDEV
  no SCOPEWG&SCOPEDEV
  no SCOPESG&SCOPEDEV
  no SCOPEWG&SCOPEQF
  no SCOPESG&SCOPEQF
  no SCOPESG&SCOPEWG

  // two ops are in scope with each other if they are both scope device or are
  // in the "same group" and have "group or greater" scope.
  inscope = (SCOPEDEV -> SCOPEDEV) +
            (sqf & ((SCOPEDEV+SCOPEQF) -> (SCOPEDEV+SCOPEQF))) +
            (swg & ((SCOPEDEV+SCOPEQF+SCOPEWG) -> (SCOPEDEV+SCOPEQF+SCOPEWG))) +
            (ssg & ((SCOPEDEV+SCOPEQF+SCOPEWG+SCOPESG) -> (SCOPEDEV+SCOPEQF+SCOPEWG+SCOPESG)))

  // mutually ordered atomics are to the same location and same reference and in scope
  mutordatom = (sloc & sref & (A -> A) & inscope) - iden

  posctosem = po & ((SC0 -> SEMSC0) + (SC1 -> SEMSC1))
  posemtosc = po & ((SEMSC0 -> SC0) + (SEMSC1 -> SC1))

  // A's scoped modification order:
  // - must be a strict partial order
  // - must relate all mutually ordered atomic writes at the same location
  strict_partial_order[asmo]
  rai[asmo] = ((A&W) -> (A&W)) & mutordatom

  // Release sequence starts with an atomic release followed by the reflexive
  // transitive closure of immediate asmo limited to RMWs. Leaving out C++'s
  // same-thread-atomic-write aspect of release sequences. hypors is the same
  // for "hypothetical release sequences" where the release happens in a fence
  // earlier in the same invocation.
  rs = (stor[REL&A]) . *((imm[asmo]) . (stor[R&W]))
  hypors = (stor[W&A]) . *((imm[asmo]) . (stor[R&W]))

  // From-read (aka reads-before) are (read,write) pairs where the read reads a
  // value before the write in atomic modification order (i.e. the inverse of
  // reads-from joined with asmo). For reads that read-from init, they
  // from-read all writes at the same location.
  fr = (~rf . asmo) + ((stor[RFINIT]) . sloc . (stor[W])) - iden

  // synchronizes-with is similar to C++, with an additional case for fence->cbar->cbar->fence
  sw = inscope & (
       // atomic->atomic
       ((stor[REL&A]) . rs . (rf & mutordatom) . (stor[ACQ&A])) +
       // fence->atomic
       ((stor[REL&F]) . posemtosc . (stor[A&W]) . hypors . (rf & mutordatom) . (stor[ACQ&A])) +
       // atomic->fence
       ((stor[REL&A]) . rs . (rf & mutordatom) . (stor[A&R]) . posctosem . (stor[ACQ&F])) +
       // fence->fence
       ((stor[REL&F]) . posemtosc . (stor[A&W]) . hypors . (rf & mutordatom) . (stor[A&R]) . posctosem . (stor[ACQ&F])) +
       // fence->cbar->cbar->fence
       // (stor[CBAR]) terms are redundant because scbarinst is an equivalence relation on scbarinst,
       // but they make the sequence of instructions more clear.
       ((stor[REL&F]) . (rc[po]) . (stor[CBAR]) . (scbarinst & inscope - iden) . (stor[CBAR]) . (rc[po]) . (stor[ACQ&F])))

  // inter-thread-happens-before =
  //   system-synchronizes-with
  //   synchronizes-with where both sides have SC in semantics
  //   SC||SEMSC -> programorder -> release<SEMSC>
  //   acquire<SEMSC> -> programorder -> SC||SEMSC

  ithbsemsc0 = ^(ssw +
                 (stor[SEMSC0]).sw.(stor[SEMSC0]) +
                 (stor[SC0+SEMSC0]).po.(stor[REL&SEMSC0]) +
                 (stor[ACQ&SEMSC0]).po.(stor[SC0+SEMSC0]))

  ithbsemsc1 = ^(ssw +
                 (stor[SEMSC1]).sw.(stor[SEMSC1]) +
                 (stor[SC1+SEMSC1]).po.(stor[REL&SEMSC1]) +
                 (stor[ACQ&SEMSC1]).po.(stor[SC1+SEMSC1]))

  ithbsemsc01 = ^(ssw +
                  (stor[SEMSC01]).sw.(stor[SEMSC01]) +
                  (stor[SC0+SC1+SEMSC01]).po.(stor[REL&SEMSC01]) +
                  (stor[ACQ&SEMSC01]).po.(stor[SC0+SC1+SEMSC01]))

  // happens-before = ithb<SC> or program order
  hb = ithbsemsc0 + ithbsemsc1 + ithbsemsc01 + po

  // Chains of instructions that produce the desired availability/visibility.
  // Example: An AVWG that happens before an AVSH in the same workgroup is
  // enough to make the original write available to the shader domain.
  // "chains & ..." effectively "turns off" nontrivial chains when the feature
  // is not supported by ANDing with the identity relation.
  avsg = stor[AVSG]
  avwg = (chains & (rc[avsg . (hb & ssg & avvisinc)])) . (stor[AVWG])
  avqf = (chains & (rc[avsg . (hb & ssg & avvisinc)]) . (rc[avwg . (hb & swg & avvisinc)])) . (stor[AVQF])
  avsh = (chains & (rc[avsg . (hb & ssg & avvisinc)]) . (rc[avwg . (hb & swg & avvisinc)]) . (rc[avqf . (hb & sqf & avvisinc)])) . (stor[AVSHADER])
  avdv = stor[AVDEVICE]

  vissg = stor[VISSG]
  viswg = (stor[VISWG])     . (chains & (rc[(hb & ssg & avvisinc) . vissg]))
  visqf = (stor[VISQF])     . (chains & (rc[(hb & swg & avvisinc) . viswg]) . (rc[(hb & ssg & avvisinc) . vissg]))
  vissh = (stor[VISSHADER]) . (chains & (rc[(hb & sqf & avvisinc) . visqf]) . (rc[(hb & swg & avvisinc) . viswg]) . (rc[(hb & ssg & avvisinc) . vissg]))
  visdv = stor[VISDEVICE]

  locord = ((R+W)->(R+W)) & sloc & // relates memory accesses to the same location
           ((hb & sthd & sref) + // single-thread case
            asmo + // mutually-atomic case
            ((stor[R-PRIV]) . hb . (stor[R+W-PRIV])) + // RaR, WaR (non-private)
            ((stor[R]) . ^ssw . (stor[R+W])) + // RaR, WaR (any)
            (sref & ((stor[W-PRIV]) . (rc[po] & avvisinc) . avsg . (hb & ssg) .                               (stor[W-PRIV]))) + // WaW (via subgroup instance domain)
            (sref & ((stor[W-PRIV]) . (rc[po] & avvisinc) . avsg . (hb & ssg) . vissg . (rc[po] & avvisinc) . (stor[R-PRIV]))) + // RaW (via subgroup instance domain)
            (sref & ((stor[W-PRIV]) . (rc[po] & avvisinc) . avwg . (hb & swg) .                               (stor[W-PRIV]))) + // WaW (via workgroup instance domain)
            (sref & ((stor[W-PRIV]) . (rc[po] & avvisinc) . avwg . (hb & swg) . viswg . (rc[po] & avvisinc) . (stor[R-PRIV]))) + // RaW (via workgroup instance domain)
            (sref & ((stor[W-PRIV]) . (rc[po] & avvisinc) . avqf . (hb & sqf) .                               (stor[W-PRIV]))) + // WaW (via queue family instance domain)
            (sref & ((stor[W-PRIV]) . (rc[po] & avvisinc) . avqf . (hb & sqf) . visqf . (rc[po] & avvisinc) . (stor[R-PRIV]))) + // RaW (via queue family instance domain)
            (sref & ((stor[W-PRIV]) . (rc[po] & avvisinc) . avsh . (hb      ) .                               (stor[W-PRIV]))) + // WaW (via shader domain)
            (sref & ((stor[W-PRIV]) . (rc[po] & avvisinc) . avsh . (hb      ) . vissh . (rc[po] & avvisinc) . (stor[R-PRIV]))) + // RaW (via shader domain)
            (        (stor[W])      . (hb & avvisinc)     . avdv . (hb      ) .                               (stor[W])) +       // WaW (via device domain)
            (        (stor[W])      . (hb & avvisinc)     . avdv . (hb      ) . visdv . (hb & avvisinc)     . (stor[R])))        // RaW (via device domain)

  // data race = same location, at least one is a write, not equal,
  // not mutually ordered atomics, not location ordered either direction
  dr = sloc & ((W -> W) + (W -> R) + (R -> W) - mutordatom - iden - rai[locord])

  // visible to = location ordered W->R with no intervening write (W->W->R)
  visto = imm[(stor[W]) . locord] . (stor[R])
}

pred consistent[X:Exec] {
  // consistency: locord, rf, fr, asmo must not form cycles
  is_acyclic[X.locord + X.rf + X.fr + X.asmo]

  // consistency: non-atomic reads must read-from a value that is still visible
  X.rf . (stor[X.R-X.A]) in imm[(stor[X.W]) . (X.locord)]
}

pred racefree[X:Exec] {
  no X.dr
}

pred locordcomplete[X:Exec] {
  // In a race-free program, any reads and writes at the same location must
  // be ordered by locord and/or mutordatom
  rai[X.locord]+X.mutordatom-((X.R-X.W)->(X.R-X.W)) = X.sloc-iden-((X.R-X.W)->(X.R-X.W))
}

// Asserts that should be true for all executions:

// locord only relates operations at the same location
assert AssertLocordSameLoc { all X : Exec | X.locord in X.sloc }

// locord is acyclic
assert AssertLocordAcyclic { all X : Exec | !consistent[X] || is_acyclic[X.locord] }

// if (consistent && racefree) locordcomplete
assert AssertLocordComplete1 { all X : Exec | !(racefree[X] && consistent[X]) || locordcomplete[X] }

// if (locordcomplete && consistent) racefree
assert AssertLocordComplete2 { all X : Exec | !(locordcomplete[X] && consistent[X]) || racefree[X] }

// can't synchronize-with yourself
// (too slow to run, in practice)
assert AssertNoSwSelf { all X : Exec | !consistent[X] || no ((X.sw) & iden) }

// no (W->W->R) in visto
assert AssertVisTo { all X : Exec | no ((X.visto) & ((stor[X.W]) . (X.locord) . (stor[X.W]) . (X.locord) . (stor[X.R]))) }
