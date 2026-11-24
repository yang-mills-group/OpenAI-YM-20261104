import YM.Integration.WilsonSubcriticalScalarSource

/-! The Laurent counterterm and full subtracted MS trajectory of the actual zero-grade
mark, on the given deck and bulk.  In particular this does not change to the canonical
MS deck used by the historic unit constructor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSubcriticalMSStationary
open Filter Topology Set Function MeasureTheory MS MS.Logarithm MS.Land
open MS.Plane MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Convolve MS.Book.Program MS.Dock MS.Garment.Wick
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Arts MS.Halo MS.Arc MS.Garment MS.Hem MS.Rock MS.Rock.Path MS.Alps
open MS.Plane.Wire MS.Arts.Pilot MS.Rock.Oceans MS.Color MS.Shine MS.Hem.Mell FVA2 FVA2.ColorCode MS.SpinCode
open MS.Menus MS.Motif MS.Motif.Literal MS.Emit MS.Local.Physical MS.Rake ArchTurn WilsonSubcriticalRichOptics
open scoped Topology Classical ContDiff
variable {G:Gauge} {B:Deck G} (A:Booked B) (j:Plaid B 0)

def scalar (n:ℕ):ℂ:=if n=0 then valueAtUnit j else 0
def bare (n:ℕ):Coat G:=gloss (Literal.linear (Mob G) (A.optics 0 j)) n

def stationary (n:ℕ):Flats G:=Finsupp.single 0 (bare A j n)

private theorem exact_bare (n:ℕ)(z:ℂ):(bare A j n) z=Frost.pile (scalar j n):=by
  unfold bare;rw [issued A j];unfold gloss;rw [hiss,Finsupp.single_apply];unfold scalar
  by_cases h:n=0
  · simp [h]
  · rw [if_neg (Ne.symm h),if_neg h];ext i l;cases l <;> rfl

private theorem cost (n:ℕ):Count (bare A j n) 0 ∧ kPrice (Frost.pile (G:=G) (scalar j n)) ∧ Cap0 false 0 0 (bare A j n):=by
  have he:Badge false (bare A j n) 0 0:=Ele.grows (A.law 0 j) n
  rw [funext (exact_bare A j n)] at he ⊢
  obtain ⟨hh,_,fine⟩:=give (K:=Frost.pile _) he
  exact ⟨he.born,hh,fine,Eventually.of_forall (fun _=>(show Issue 0 (Frost.pile (G:=G) _) from fun _ l hl=>by cases l;simp at hl;rfl))⟩

private theorem drive (bulk:T (Flats G))(n:ℕ):platform bulk n (stationary A j)=0:=by
  unfold platform;refine Finset.sum_eq_zero fun v _=>?_ ;unfold drive0;generalize bulk v.1=J
  induction J using Finsupp.induction_linear with
  | zero=>rw [map_zero,LinearMap.zero_apply]
  | add p q hp hq=>rw [map_add,LinearMap.add_apply,hp,hq,add_zero]
  | single k z=>
    let P:=tapeB (squad (A0 G 0)) z
    rw [TreeN,explode,Finsupp.lsum_single];change blast k P _=0;rw [stationary,blast_sl]
    have h:P (bare A j v.2)=0:=funext fun x=>by change squad (A0 G 0) (z x) (bare A j v.2 x)=0;rw [exact_bare,Frost.pion]
    rw [h,Finsupp.single_zero]

private theorem lifted (n:ℕ)(s y:ℝ):Lift (Parade (stationary A j n) 0 y s) (Frost.pile (scalar j n)):=by
  obtain ⟨hb,h,_⟩:=cost A j n;rw [stationary,pureP _ hb,funext (exact_bare A j n)];exact Lift.stays h

theorem solution (bulk:T (Flats G)):comet 0 0 bulk (gloss (Literal.linear (Mob G) (A.optics 0 j))) (stationary A j) 0:=by
  intro n;obtain ⟨counted,regular,cap⟩:=cost A j n
  have hh:ClockD false 0 0 (stationary A j n):=Cap0.heap.single cap 0
  refine ⟨⟨0,?_,hh,Cap0.zero⟩,False.elim⟩;rw [drive,zero_add]
  have charged:Live (bare A j n):=by rw [funext (exact_bare A j n)];exact Live.stays regular
  exact (joint_static counted charged).via (pact_sym (pact0 ⟨(0:ℤ)-2,by omega,clockCap (mine hh (joint_static counted charged).toll).eye⟩))

theorem measured (M:MS_Data G A) : M.poles 0 j=0 ∧ ∀n:ℕ, Pact (M.marks 0 j n) (stationary A j n):=
  unique_M (M.markOK 0 j) (solution A j M.bulk) (fun _ _=>EventuallyEq.rfl)

theorem archived (M:MS_Data G A) (n:ℕ)(s y:ℝ):Archive 0 (M.marks 0 j) n (y,s)=coin (scalar j n):=by
  have model:=solution A j M.bulk
  rw [archive_h (measured A j M).2 (fun k=>Dock.gang (M.markOK 0 j k)|>.dost) (fun k=>Dock.gang (model k)|>.dost)]
  have eq:hereZ 0 (stationary A j n) s y=Frost.pile (scalar j n):=Lift.unique (live0 (fun a b=>⟨_,lifted A j n b a⟩)) (lifted A j n s y)
  exact congr_fun eq 0

end YM.Integration.WilsonSubcriticalMSStationary
