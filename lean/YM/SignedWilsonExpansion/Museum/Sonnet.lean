import YM.SignedWilsonExpansion.Museum.Genre
/-! # Physical orders through the LITERAL HETER-CAP TUPLE. Also explain each VIEWER. They do not replace the measures on cut & period. -/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Museum
open FullVolume Function Filter Set MeasureTheory Lattice Wilson RG Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset OPE OPE.Orbits
open PhysicalNext.Repeat.Legato Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale.Level Spec PhysMS PhysMS.Frame
open Next.UVStress Kane.Tilted Scale Rose
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G){n d:ℕ}{o:Extraction.Order}{S:Table R.family.book}(F:Final R.family o S)(A:Museum.Portfolio S F.room.kernel.spin)(W:ℝ→tower S)(r:ℝ)

variable (b:Caps n) (m:Finset (Fin n))(t:∀i,Sec G (b i))
local notation "Q" => Finset (Fin n)
abbrev coversB: ∀ i, Sec G ( b i ) := fun i=> if i∈ m then t i else leaf G (b i)
abbrev stringsB (i:Fin n): R.family.book.Token:= ⟨b i,gala R F A W r (b i) ( t i )⟩
abbrev orchestra (x:Points n)(v:Viewers F): ℂ:= S.classMoment (spectator F v) b (r • x) (fun i=> walk W r (b i) (t i))
local notation "ψ" => stringsB R F A W r
lemma entranceB (x:Points n) (s:r • x∈ conf n) (u:Viewers F) : orchestra R F W r b t x u=(spectator F u).read ( r • x ) (ψ b t):= by
    rw [← S.at_project ( spectator F u ) ( spectate F u ).laws.toSymmetric (spectate_respects F u) s]; change _=S.classMoment (spectator F u) b (r • x) (fun i=> S.project (b i) ((A (b i)).desk (walk W r (b i) (t i)))); simp_rw [Arm.era]
lemma applause (v:Viewers F)(x:Points n)(s:r • x∈ conf n): orchestra R F W r b t x v = (glance F v) (viewing F (r • x).ofLp (ψ b t)):=by rw [entranceB R F A,glance_sees F _ _ _ s,named_fin (spectator F v) (spectate F v).laws.toSymmetric _ s]; exact s
lemma littoral (h:∀ i:Fin n,walk W r (b i) ( Normalize.leaf G _ )= S.unit (b i)) (N p:ℕ)(s:∀ i:Fin n,R.family.ref (b i)≤N)(u:Ps N p R.family n) : R.family.numeric N p (ψ b (coversB b m t)) u= ∫ U,(∏ i∈m,R.family.seen (ψ b t i) (u i) U) ∂(law G _ (R.family.beta N p)):=by
   rw [Family.num]; apply integral_congr_ae; apply Eventually.of_forall; intro U; generalize_proofs; symm
   refine Eq.trans ( Finset.prod_congr (g:=fun i=>R.family.seen (ψ b (coversB b m t) i) (u i) U) rfl (fun i hi=> ?_)) ( Finset.prod_subset m.subset_univ ?_ ); · simp only [ stringsB,coversB,hi,if_true ]
   intro i hi hj; simp only [ stringsB, coversB, hj, if_false ]; have he: gala R F A W r (b i) (Normalize.leaf G (b i))= R.family.refUnit (b i):=by rw [gala,LinearMap.comp_apply,LinearEquiv.coe_coe,h,(A _).dry]; rfl
   rw [he]; exact congr_fun ( R.family.constant R.makes (b i) (s i) (u i) ) U
variable (f:Test n)(φ:(Finset (Fin n)→ℂ)→ℂ)(h:G.Simple) (hv:PositionsUV R.family Extraction.Sequence.full)(hX:(Homes.track o).PointLimits R.family S) (hr:0 < r) (ht:Continuous φ)
include h hv hX hr ht
lemma maskedLife : (Homes.track o).limits (fun p=>Prism R.family.S (tsupport f) p r) (summit R.family f r φ fun m=> ψ b (coversB b m t) ) (f.applyTo fun x=> φ fun m=> orchestra R F W r b (coversB b m t) x none ):= by
    let v:Finset (Fin n)→ Fin n→ R.family.book.Token:=fun m=> stringsB R F A W r b (coversB b m t)
    let e(x:Points n):= φ fun s=> orchestra R F W r b (coversB b s t) x none; have he: f.applyTo e=f.applyTo (fun x=> φ fun j=> S.read (r • x) (v j)):= Test.apply_eq f (fun x hx=> congr_arg φ (funext fun i=> entranceB R F A W r b _ x (Work.A05.smul_conf hr hx) none))
    change Extraction.Order.limits _ _ _ (f.applyTo e); rw [he]; exact sequenceP f r φ ht R h hv F.room.kernel.smooth hX v hr
end YM.SignedWilsonExpansion.Museum
