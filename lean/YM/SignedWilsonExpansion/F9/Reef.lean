import YM.SignedWilsonExpansion.F9.Bowler
import YM.Integration.WilsonIndependentMatchedOrbitReading
import YM.Integration.WilsonIndependentRawPeriodPower
import YM.Integration.WilsonIndependentRawWordGeometry
import YM.WilsonCoeffUV.Product.Report.Center
import YM.RegulatorIR.Profiles.Staple
/-!
# Actual generic finite Cloth opening at the auxiliary inversion epoch

Generalizes the raw named stencil stop (Width note density still charged through
`original-handoff/WilsonIndependentSpoutPhysicalOrbit`). Not unrestricted Start or replacing
one clock convention with another one. Here the top symbol is proved to be the *same* inside
Birth/with perturbative power, then encounters use a fixed finite Column in all dates (Clock,
Gauge price & Lantern reusable). We re-use the nonperturbative estimates only on the long
physical box, indicate where the period/clock change is invoiced separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 730000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.Reef
open Function Filter Finset Lattice Laurent Matrix Wilson RG Gauge Source Labels Exterior
open XSpace PertExtension.Series.Radial Blue Power Bank Soil FreeResolvent Cosmos Cosmos.Polestar Embroider Tree
open RegulatorIR RegulatorIR.Profiles RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Binding
open RegulatorIR.Diagram RegulatorIR.Prim RegulatorIR.Cluster RegulatorIR.Budget RegulatorIR.Budget.Packet
open PertExtension FVA2 Integration
open PowerSeries
open scoped Classical ENNReal NNReal Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{W I:Type}{n:Side}
variable (P:Pill G)
-- sufficient raw mark on the cover (full replica, before crop)
def brand : Portrait G:=fun _=> P.f
lemma brand_hot : LocalStamp (brand P) P.rank:=by
   obtain ⟨S,X,p,v⟩:= P.valid; refine ⟨⟨P.valid.cont.comp continuous_snd,fun _=>P.inv,?_⟩,⟨(Maskable.ends S),fun _=> Maskable.sees (S:=S) ⟨X,p,v⟩⟩, fun b=> P.bound (timber G b) ⟩ -- order defeq width check
   intro E _ _ k U h hk h0 pQ; unfold brand; simp_rw [v]; exact (p.of_le le_top).contDiffAt.comp _ (contDiffAt_pi.mpr fun i=>h _)
lemma symbol_real : ∃ T:Orders (Foot G), BasisT P.rank P.rank (brand P) T ∧ Ranks P.rank T:= stamp_symbol (brand_hot _)
def virtualP := (symbol_real P).choose
def symbolP (o:Cover):Orders (Foot G):=fun i r=> echo (carryX o) (virtualP P i r)
lemma symbol_cap (p:Cover): BasisT P.rank P.rank (convey p (brand P)) (symbolP P p) ∧ Ranks P.rank (symbolP P p):=by
   obtain ⟨H,N⟩:= (symbol_real P).choose_spec
   refine ⟨H.vayne p,fun i j alive=> N i j (fun h=> alive ?_)⟩; exact (congrArg (echo (carryX p)) h).trans echo_zero

-- Based on WilsonIndependentSpoutOrdinaryPlate in the other construction.
def periodic (y:TreeVars G n)(q:Foot G):ℝ:= ((WilsonCoeffUV.cloth G n).symm y (wrap n q.1.1,Exterior.coord q.1.2)) q.2
lemma dilate (y:TreeVars G n)(t:ℝ):periodic (t • y)=t • periodic y:= by funext q;unfold periodic; rw [map_smul]; rfl
lemma links (y:TreeVars G n): win G (periodic y)=expandAt 0 (mantle y) := by funext i; unfold win expandAt mantle; rw [Work.F03.represent_link, add_zero]; congr 1

def scout (n:Side)(v:TreeVars G n) : Ink (Woods G n)→+*Cost:= PowerSeries.map (MvPolynomial.eval v)
lemma evaluate {n:Side}(f:TreeVars G n→ℝ)(h:Green f)(y:TreeVars G n):
    scout n y (Blue.jet f)=tale (fun t:ℝ=>f (t • y)):=by
  ext1 e; unfold scout; rw [coeff_map,rayon,lore (h.of_le (by simp):ContDiffAt ℝ ∞ f 0) y]; simp only [inscription, coeff_mk]; rfl
lemma moved {n:Side}(M:Matrix (Woods G n) (Woods G n) ℝ)(v:TreeVars G n)(A:Ink (Woods G n)): scout n v (Blue.loom M A)=scout n (M*ᵥv) A:=by ext1 e; simp only [scout,Blue.loom,coeff_map]; exact cord_apply M v _

lemma seen (n:Side)(y:TreeVars G n)(o:Cover): scout n y (flash ((shifted P.letter o).1 n))=shelter P.rank (symbolP P o) (periodic y):=by
   apply mul_left_cancel₀ (a:=PowerSeries.X^P.rank) (pow_ne_zero _ X_ne_zero)
   rw [← (symbol_cap P o).1.pose]; change _ * scout n y (flash (skewV (wrap n o) (P.letter.1 n)))= _; rw [translate_value n (wrap n o) _ (P.solid.span _), moved]; let M:= spear (jog (wrap n o):Woods G n≃ Woods G n); change X^P.rank*scout n (M*ᵥ y) (flash _)= _; have he: scout n (M*ᵥ y) X=X:= map_X _; rw [← he,←map_pow, ←map_mul, P.flare, evaluate (P.reading n) (P.nearby n)]; apply congr_arg tale; funext t; unfold Halo.outing; rw [←dilate,links, ← Matrix.mulVec_smul];
   have hu(v:Config G n): expandAt 0 (Lattice.translate (wrap n o) v)= Lattice.translate o (expandAt 0 v):=by funext i; change v (wrap n i.1+0+ _,i.2)=v (wrap n (i.1+o)+ 0,i.2); rw [map_add]; simp
   unfold Pill.reading M; rw [mantle_reads,Lattice.pull_one,hu]; rfl

/- Composite of actual stencils. association fixed for all spaces. -/
variable (Y:I→Pill G) (o:I→Cover)
def foldR {A:Type}[Mul A] (vals:I→ A):Composite I→ A| .atom i=>vals i| .pair a b=> foldR vals a*foldR vals b
def homeRank (V:Composite I):= V.accounts (Pill.rank ∘ Y)
def oblige (V:Composite I):= Gather V fun i=> convey (o i) (brand (Y i))
def seed (V:Composite I):Orders (Foot G):= V.product fun i=>symbolP (Y i) (o i)
lemma composed (V:Composite I): BasisT (homeRank Y V) (homeRank Y V) (oblige Y o V) (seed Y o V) ∧ Ranks (homeRank Y V) (seed Y o V) :=
    ⟨Profiles.BasisT.given V _ (fun _ _=>(symbol_cap ..).1) (fun _ _=>(symbol_cap ..).2), V.ranks _ (fun _ _=>(symbol_cap ..).2)⟩
-- actual WCU opening stencil
def welcome : Composite I→ Era G ℝ | .atom i=> shifted (Y i).letter (o i)|.pair a b=> agateV (welcome a) (welcome b)
lemma kinetic (V:Composite I): Auth (homeRank Y V) (welcome Y o V):=by induction V with | atom i=> exact (Y i).solid.shifted _| pair a b p q=> exact p.manor q
lemma minded (V:Composite I)(v:TreeVars G n): scout n v (flash ((welcome Y o V).1 n))= shelter (homeRank Y V) (seed Y o V) (periodic v):=by
    induction V with
    | atom i=> exact seen ..
    | pair a b p q=>
       have X:=composed Y o a; have y:=composed Y o b; change scout n v (flash (woad _ _))=shelter (homeRank Y a+homeRank Y b) (accord (seed Y o a) (seed Y o b)) _; rw [woadap _ _ (finite_shell ((kinetic Y o a).span n)) (finite_shell ((kinetic Y o b).span n)), map_mul,p,q,shelter_pair _ X.1.canopy y.1.canopy X.2 y.2]

section stereo
-- general, costs paid later. binding.Termination not asymptotic tail by itself
open RegulatorIR.Laplace
open Integration.WilsonIndependentMatchedOrbitReading (originalClock)
variable (R:Period) (T:R.Tree)
protected def offer (V:Composite I): Config G R.side→ ℝ:= foldR (fun i=> WardBin.places (wrap R.side (o i)) (Y i).f) V
protected def main (V:Composite I):Bare.Series T G:= foldR (fun i=> StationA.propose T (wrap R.side (o i)) (Y i)) V
lemma mushy (V:Composite I): ContDiff ℝ ω ((Reef.offer Y o R V) ∘ T.links) :=by induction V with|atom i=> exact StationA.flies T (Y i).valid _ | pair a b p q=> exact p.mul q
lemma offered (V:Composite I): Orb.PreTest (Reef.offer Y o R V):= by induction V with| atom i=> exact StationA.candle (Y i) _| pair _ _ h h'=>exact FormalOPE.RG10.InversionTop.Uses.pre_mul h h'
lemma offering (V:Composite I): X^ homeRank Y V * Reef.main Y o R T V=BareOrb.stencil T (Reef.offer Y o R V):=by
   induction V with
   | atom i=> exact StationA.apex ..
   | pair a b p q=>
       change X^ (_+_)*(Reef.main Y o R T a* Reef.main Y o R T b)=BareOrb.stencil T (Reef.offer Y o R a*Reef.offer Y o R b); rw [pow_add,StationA.mergeBook T (mushy Y o R T a) (mushy Y o R T b),←p,←q]; unfold homeRank; ring
lemma enrolled (V:Composite I): vital R.side (oblige Y o V) = Integration.WilsonIndependentMatchedOrbitReading.insert (Reef.offer Y o R V):=by
   induction V with
   | atom i=>
       funext t v h; have hp: Lattice.translate (o i) (orbLift v ∘ around R.side)= expandAt (wrap R.side (o i)) (Orb.liftLinks v):=by
           funext e; change Orb.liftLinks v (wrap R.side (e.1+ o i),e.2)=Orb.liftLinks v (wrap R.side _+_,e.2); rw [map_add]
       change (Y i).f (Lattice.translate (o i) _) = _; rw [hp]; rfl
   | pair _ _ h h'=> exact funext fun x=> funext fun t=> funext fun u=> congr_arg₂ (· * ·) (congr_fun (congr_fun (congr_fun h x) t) u) (congr_fun (congr_fun (congr_fun h' x) t) u)
-- same encounter identity as WilsonIndependentMatchedClosedPlan.actual
theorem sustains {n:Side}(he:Even n.val)(O:Config G n→ℝ)(h:Orb.PreTest O): Plan G n (Integration.WilsonIndependentMatchedOrbitReading.insert O) := by
  refine ⟨?_,?_,?_⟩
  · intro k hk u t
    change O (orbLift (goat k u))=O (orbLift u)
    rw [goat_lift k u hk,h.gauge _ hk]
  · have links:Continuous (Orb.liftLinks (K:=G.El) (n:=n)) := by
      apply continuous_pi; intro e; unfold Orb.liftLinks; split <;> fun_prop
    exact (h.continuous.comp links).comp (continuous_fst.comp continuous_snd)
  · change ContDiffAt ℝ ∞ (fun z: RegulatorIR.Laplace.Meadow G Empty × ℝ × Meadow G (Orb.OEdge n)=> O (Orb.liftLinks (PertExtension.Chart.expLinks G _ z.2.2))) 0
    apply FVA2.OrbGerm.adapt he h
    intro i; apply OrbGerm.AtBase.exp (f:=fun z:Meadow G Empty × ℝ × Meadow G (Orb.OEdge n)=>z.2.2 i)
    · fun_prop
    · rfl
lemma landed (p:ℕ)(V:Composite I): PowerSeries.coeff p (Bare.normalized T G (Reef.main Y o R T V)) = ↑(plotPT originalClock (vital R.side (oblige Y o V)) (homeRank Y V) p) := by
    have h:=offered Y o R V; let X':= Reef.offer Y o R V; let r:= homeRank Y V
    have he := (Eq.symm (StationA.tunic T (G:=G) r (Reef.main Y o R T V))).trans ((congr_arg (Bare.normalized T G) (offering Y o R T V)).trans (Integration.WilsonIndependentMatchedOrbitReading.diagram T X' h (sustains (even_iff_two_dvd.mpr R.even) X' h)))
    rw [enrolled]; have ht:= congr_arg (PowerSeries.coeff (r+p)) he
    simpa [FVA2.TaylorWick.into,coeff_X_pow_mul',plotPT,Nat.le_add_right] using ht
end stereo
end YM.WilsonCoeffUV.Mer.Xa.Reef
