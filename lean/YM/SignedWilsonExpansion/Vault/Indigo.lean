import YM.SignedWilsonExpansion.Vault.Dossier
/-! Terminal coupons for ANY combination (common horizon and exact energy bookkeeping). Restoration all powers of regular action on *this very* combination, full-stop at `oldT` and beam records kept along.L. No UV limit until reader signs every face. Compile separate from `Estate` (tester) but on its Diary. -/
set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 380000
noncomputable section
namespace YM.Integration.Election.VaultM.Till.Dossier
open Function Finset Filter MeasureTheory Extraction Climb Spec Table Next.UVStress Trace.Pilot PhysMS Maxwell Extra.FD
open RG.Supply PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot Asymptotics
open SignedWilsonExpansion SignedWilsonExpansion.Homes Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank RG PowerSeries SignedWilsonExpansion.Purchases UVClock Schedules
open XSpace Commission Dancer Dancer.Drawing Dancer.Shell Dancer.Fort Dancer.Stitch Dancer.Motif Camera SignedWilsonExpansion.Vault
open OPE.Therm Lattice Wilson RG05Readout RG05Readout.Address RG05Readout.Records Marker Cells HeartT HeartT.Spritz
open Precision XSpace.Normalize WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ WilsonCoeffUV.Cosmos.Polestar
open FVA2 FVA2.Dframe XSpace.Cirrus FVA2.Register
open Pert.Asymptotics Logwood HeatS StageG Exporter.Loans
open scoped Topology ContDiff Classical BigOperators ENNReal
open PRAY Fire Diary Dancer.Supper SignedWilsonExpansion.Purchases.HalfRoof PurchVoice
variable {G:Gauge}{R:PhysicalNext.Repeat.Legato.Run G}{h:G.Simple}{e:Axis}{T₀:Campaign R}{W₀:Campaign.Pillars R T₀}
variable {P:PRAY R h}{D:ℕ}{W:P.Wings D}
universe u₀
variable {σ:OrderS G}{ε:ℝ}(p:PaidP.{u₀} e h ε σ R T₀ W₀) {Z:WilsonPrescription G} {u:Scarf G D}
variable {a:Axis}{ι:Type}{L:Filter ι}{r t:ι→ℝ} {M:Diary W L r t}{S:Plans a}
variable {hv:Author.CameraT S}{money:ℕ}(X:Dossier W M S money hv)(b:Draft G D S)
local notation "C₀" => R.family
local notation "Fℓ" => reporter W M
local notation "κ" => filing W M X.K
local notation "S₀" => R.family.path.levels
local notation "LP" => alongT L P.f
-- coupon describes the *symbolic* unit after full eligibility. Bundle power heterogeneity allowed.
abbrev Shelves {a:Axis}{D:ℕ}{G:Gauge}{P:Plans a}(b:Draft G D P):Type:= (i:Fin (Draft.bill b))→ Sec G ( stampK b i )
abbrev portionB (y:Shelves b):= priceY (stampK b) y (fun i=> X.phaseB ( pays b i ) univ)
abbrev portionW (y:Shelves b):= priceY (stampK b) y (fun i=> X.upperB ( pays b i ) univ)
abbrev χP:= needH money (S.arity+2) D ( window W ) X.K
abbrev carpet (y:Shelves b)(s:Finset (Fin (Draft.bill b))) : Shelves b:= fun j=> if j∈s then y j else leaf G (stampK b j)
-- Common `χ` read from election. ALL cells, caps.*
structure Binder (b:Draft G D S) (z:Visual ι)(x:Fin (Draft.bill b)→ Cover) :Prop where
    sold : ∀ y:Shelves b, Comb C₀ (stampK b) x R.metals.O (Emit W M b z y) (Elect W M X.axes X.K b z y) X.Pre X.overhead X.Out (reserveH (stampK b) y) (X.portionB b y) (X.portionW b y) X.χP (Fℓ z.1) (κ z.1) (X.V z.1) X.oldT ( X.total b ) z.2.1 z.2.2
    units : ∀ (p:Shelves b)(s:Finset ( Fin (Draft.bill b) )), let y:=carpet b p s
           stemN R.family (stampK b) x ( Emit W M b z y ) ( Fℓ z.1 ) z.2.1 z.2.2 univ= stemN R.family (stampK b) x ( Emit W M b z p ) ( Fℓ z.1 ) z.2.1 z.2.2 s ∧
           stemK R.family (stampK b) x ( Elect W M X.axes X.K b z y ) ( Fℓ z.1 ) z.2.1 z.2.2 (κ z.1) univ= stemK R.family (stampK b) x ( Elect W M X.axes X.K b z p ) ( Fℓ z.1 ) z.2.1 z.2.2 (κ z.1) s
open Trace.Physical.Germ Trace.Physical.GermGraph
abbrev ready (s:ι)(d:Slice D)(b: Bool)(n p:ℕ) := ReadyReturn C₀ d.val n p ( rootJ W M b s ) ( shapeS W M X.K b s ) ( X.axes b (s,n,p) d.val )
abbrev fine (s:ι)(d:Slice D)(b: Bool)(n p:ℕ) := (X.ready s d b n p ∧ rootJ W M b s+ shapeS W M X.K b s < n) ∧ (( station W M b ) s).Given (track P.f) P.H ( M.home b s ).val
variable (hr:Tendsto r L trail)
include p hr
lemma growing (u:Slice D) (s:Bool) : ∀ᶠ i in L,∀ᶠ f:ℕ in atTop,∀N>filing W M X.K i,X.fine i u s N f:=by
    let x:= compare_pivot hr ( M.holds s ); let θ:= W.actualB L (M.home s) x.1; have ζD: 0<D:=lt_of_lt_of_le u.2 (Nat.le_of_lt_succ u.val.isLt); have he: Glow R.family.path.levels r (cck G ∘ r) L ( rootJ W M s ):=( X.install p hr ).gear s ζD hr p.receiptsP.2; let z:= radius_clock h hr; have hp:= UVClock.fee_Θ z R.family.path.levels h ( epoch_wave z EventuallyEq.rfl he ); filter_upwards [θ.2, hp.eventually (open_late C₀ h u.val),X.calls] with i v w φ; filter_upwards [φ] with H hw N ht; have hm:rootJ W M s i+shapeS W M X.K s i < N:= congr_fun ( filed W M ζD s X.K ) i |>.trans_lt ht; exact ⟨ ⟨ ⟨ hw N ht u s, w H, hm.le⟩, hm ⟩, v ⟩ -- issues order
omit p hr
lemma Fine.shelf {t:Bool} {u:Slice D}{z:Visual ι} (hV:X.fine z.1 u t z.2.1 z.2.2) : let a:=u.val.val; (∀ j, R.family.O z.2.1 z.2.2 ( emitsσ W M z.1 t a ( leaf G a ) z.2.1 z.2.2 ) j=1 ) ∧ votedσ W M X.axes z X.K t a ( leaf G a )=( (C₀).labels.level a).e0:=by
    intro a; let p:=hV.1.1; let A:= X.axes t z a; let k:=rootJ W M t z.1; let V:= shapeS W M X.K t z.1; let g:k ≤ k+V:= Nat.le_add_right ..; have hz:k + V < z.2.1:= hV.1.2; have hs: (κ z.1)=k+V:= (congr_fun ( filed W M (lt_of_lt_of_le u.2 (Nat.le_of_lt_succ u.val.isLt)) t X.K) z.1).symm; let x: emitsσ W M z.1 t a ( leaf G a ) z.2.1 z.2.2=R.family.refUnit a:= microphone_unit R.family R.makes hV.2 ((Nat.le_of_lt_succ u.val.isLt).trans ( W.book ( M.home t z.1 ) ).fits) ( lt_of_le_of_lt g hz ) _; unfold votedσ; erw[x]; rw [hs]; obtain ⟨P⟩:= issueQ R h p.late.post hz.le z.2.2; exact ⟨fun t=> R.family.constant R.makes _ ( p.late.post.trans ( g.trans hz.le )) t,unitsK R.family R.makes _ p P⟩
private lemma Fine.linear {t:Bool} {u:Slice D} {z:Visual ι} (hV:X.fine z.1 u t z.2.1 z.2.2) : let a:=u.val.val;
    IsLinearMap ℂ (fun y=> emitsσ W M z.1 t a y z.2.1 z.2.2) ∧ IsLinearMap ℂ (fun y=> votedσ W M X.axes z X.K t a y) :=by
    intro a; let P:= hV.1.1; let S: Sec G a→ₗ[ℂ] R.family.label a := ((( station W M t ) z.1).microphone z.2 a).comp ((((Free.fields R.family.labels a)).symm).toLinearMap); let A:= X.axes t z a; let N:=z.2.1; let q:= z.2.2; let Y:= IsLinearMap.mk' _ ( save_linear R.makes P.late ( (Nat.le_add_right .. ).trans P.age ) ); let F:= ((R.family.S.a ( filing W M X.K z.1 ):ℂ)^a)⁻¹ • ( A.symm.toLinearMap.comp (Y.comp S)); exact ⟨ S.isLinear,( F ).isLinear ⟩
-- 
private lemma units_l {α :Type*} [Fintype α](s:Finset α) {x y:α→ℂ}(f:∀i∈s,x i=y i) (z:∀i∉s,x i=1): ∏ i,x i=∏i∈s, y i:= by rw [← Finset.prod_subset ( subset_univ s ) ( fun i hi H=> z i H ) ]; exact Finset.prod_congr rfl f
set_option maxHeartbeats 600000 in
lemma Fine.fitter {z:Visual ι}
    (T:∀ (t:Slice D) (s:Bool),X.fine z.1 t s z.2.1 z.2.2) (x:Fin (Draft.bill b)→ Cover)(s: Finset (Fin (Draft.bill b))) (y:Shelves b) : let p:= carpet b y s;
    stemN R.family (stampK b) x ( Emit W M b z p ) ( Fℓ z.1 ) z.2.1 z.2.2 univ= stemN R.family (stampK b) x ( Emit W M b z y ) ( Fℓ z.1 ) z.2.1 z.2.2 s ∧
    stemK R.family (stampK b) x ( Elect W M X.axes X.K b z p ) ( Fℓ z.1 ) z.2.1 z.2.2 (κ z.1) univ= stemK R.family (stampK b) x ( Elect W M X.axes X.K b z y ) ( Fℓ z.1 ) z.2.1 z.2.2 (κ z.1) s:=by
    intro p; let W(v:Fin (Draft.bill b)):=T (( Draft.port b v ).2.1) (earL b v); constructor
    · funext i; apply units_l; · intro j hj; unfold Emit p carpet micT; simp only [if_pos hj] -- note implicit
      intro j hj; unfold Emit p carpet micT; simp only [if_neg hj]; exact congr_fun ( Fine.shelf X ( W j ) |>.1 _ ) _
    funext i; apply units_l; · intro j hj; unfold fieldT Elect p carpet; rw [if_pos hj]
    intro j hj; unfold fieldT Elect p carpet; rw [if_neg hj]; specialize W j; erw [( Fine.shelf X W ).2]; exact HeartT.leafK ..
private lemma Fine.gather {z:Visual ι} (T:∀ (t:Slice D)(s:Bool),X.fine z.1 t s z.2.1 z.2.2)
    (x: Fin (Draft.bill b)→ Cover) (A:∀ t: capBox G (stampK b), let B:=pays b t; Spirits C₀ R.metals.O (stampK B) (Emit W M B z (finalist B)) (Elect W M X.axes X.K B z (finalist B)) x X.Pre X.overhead X.Out (X.phaseB B) ( X.upperB B ) X.χP (Fℓ z.1) ( X.c z.1 ) (κ z.1) (X.V z.1) X.oldT ( X.total B ) z.2.1 z.2.2 (Bequeath W M X.axes B z X.K X.V X.c x))
    (hp:X.V z.1≤X.c z.1∧ X.c z.1≤ κ z.1 ∧ X.oldT≤ X.V z.1∧ Fℓ z.1≤ κ z.1∧ κ z.1<z.2.1) : X.Binder b z x:=by
    let Θ(i:Fin (Draft.bill b)) := Fine.linear X ( T ( Draft.port b i ).2.1 (earL b i) ); let e(i:Fin (Draft.bill b)):= IsLinearMap.mk' _ ( Θ i ).1; let E(i:Fin (Draft.bill b)):= IsLinearMap.mk' _ ( Θ i ).2; refine ⟨ fun y=>?_ ,fun p s=> Fine.fitter X b T x s p ⟩; refine entire_port R.family (stampK b) x R.metals.O e y z.2.1 z.2.2 ( κ z.1 ) X.Out (X.total b) X.Pre X.χP X.overhead ( Fℓ z.1 ) ( X.V z.1 ) ( X.c z.1 ) X.oldT (fun z=>X.phaseB ( pays b z )) (fun z=>X.upperB ( pays b z )) E (fun t=> Bequeath W M X.axes (pays b t) z X.K X.V X.c x) hp R.makes (?_)
    intro i; have h:=A i; simp only [] at h; rw [ X.matched (pays b i) b rfl ] at h; exact h
include p hr
lemma issued_all : ∀ᶠ i in L,∀ᶠ p:ℕ in atTop,∀ N > filing W M X.K i,∀(x:Shake (n:=Draft.bill b)),Extraction.tag ( sizeP r (reporter W M) R.family.S i ) x ∈ ( S.m b.1 ).F→ X.Binder b (i,N,p) x:=by
   have hf:∀ᶠ i in L,∀ (q:Slice D) (s:Bool),∀ᶠ p in atTop, ∀ N>filing W M X.K i,X.fine i q s N p:= eventually_all.mpr fun q:Slice D=> eventually_all.mpr fun s: Bool=> X.growing p hr q s
   filter_upwards [X.years,hf,X.issued] with i h v x; filter_upwards [x,eventually_all.mpr (fun q:Slice D=> eventually_all.mpr (fun s:Bool=> v q s))] with p hx ht N hn x y; exact Fine.gather X b (fun q s=> ht q s N hn) x ( fun t=> hx N hn (pays b t) x y ) ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,hn⟩
end YM.Integration.Election.VaultM.Till.Dossier
end
