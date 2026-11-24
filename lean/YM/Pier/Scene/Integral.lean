import YM.Pier.Scene.Enamel
import YM.Pier.Base.Certificate
import YM.RG17.Tarmac
/-!
# Full integral (all-flag discrepancy) for the native calibrated marked readout

No zero-flag premise! Uniform over both regulators on these geometric ranges
(no K compact volume margin). Use Tarmac convention for marks on exactly
embeddable legs; bound the NATIVE scene readout by crossing to the Wilson
law, retaining all marks via the shared polynomial. Need the geometry and
stencil purchase in GracesP; the price is after label, frame & current mesh
are fixed. Expresses *still the entire normalized difference INSIDE the integral*;
includes all flag sectors, not absolute values inside or a total variation estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17.Panoramic
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Overlay
open FullVolume.Sever MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Extra.Multi Next.Rank Edition Spindle SharpGram Trace RG12 Next.UVStress
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open OPE OPE.Loom OPE.Yarn Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Patrol
open OPE.Strobe OPE.Strobe.Panoramic
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} (R:Run G) {n:ℕ} {Γ:Census (Fin n)}
local notation "C" => R.family
local notation "H" => R.family.path
local notation "T" => R.family.path.levels
variable {m k N p:ℕ}(d:Fin n→ℕ)
    (w:(j:Fin n)→ R.family.label (d j))(x:Fin n→ Site (R.family.side k p))
noncomputable abbrev recordS := fun j=> (⟨d j,w j⟩: (C).book.Token)
local notation "b" => recordS R d w
local notation "y" => attachV R k x
local notation "F₀" => skySeeds («C»:=C) b (attachV R k x) N
set_option quotPrecheck false
local notation "Y" => (C).path.rep N p
set_option quotPrecheck false
lemma seedHere (ht:k≤N) (i:Fin n): skySeeds («C»:=C) (recordS R d w) (attachV R k x) N i=abrade (C) (w i) N k p (x i) ht := by
   rw [seedNear]; change (C).seen (recordS R d w i) ((y) N i) = _; rw [show (y) N i= Push.GridApprox.anchor (C).S p ht (x i) from vect (C) k p N _ ht]; rfl

lemma rootSale (ht:k≤ N)(i:Γ.Mode) :
    (∫ U,pullDimes (p:=p) (N:=N) b (y N) i k U∂(prior G _))/(keyMass (C) N p:ℂ) =
      moment ((C).beta N p) (fineJob (fun j=>abrade (C) (w j) N k p (x j) ht) i.val) := by
   let F(j):= abrade (C) (w j) N k p (x j) ht
   have he(y':Fin n):Continuous (F y'):= (C).continuousO ..
   have hF : F₀ = F:=funext (seedHere R d w x ht)
   let X:= Accent.birth Γ (Y N) F
   have hv : (R.family.path.rep N p N).eval= bare ((C).beta N p):=(R.makes.wilson.starts N p).2
   have hg := hatCont (C) N p F he (show Continuous (Y N).eval from by rw [hv];exact bare_cont _) Γ
   have hI : Integrable X (prior G _):= hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   let l:= (Poly.get i).restrictScalars ℝ
   have hh:= correctStorm («C»:=C) (Γ:=Γ) R.makes b (y) ht
   change stamp H N p k (packStorm b (p:=p) (N:=N) (y N) k) i= moment _ (fineJob F i.val)
   rw [hh,hF]
   have hj : stamp (H) N p k (gust (H) N p N X k ht) i = stamp (H) N p N X i := by
        unfold FullVolume.Sever.stamp; congr 1
        exact (l.integral_comp_comm (gust_live H N p N X hI ht)).trans ((congr_arg (fun x:Poly Γ=> l x) (gust_sum H N p N X hI ht)).trans (l.integral_comp_comm hI).symm) -- order ht
   exact hj.trans (equality (C) p N R.makes.wilson F he i).symm

lemma sceneRoot (ht:k≤N)(s:Γ.Mode) :
    Envelope (fun U=>pullDimes (p:=p) (N:=N) b (y N) s k U/(boardMass (C) N p k U:ℂ)) ∧
      (∫ U,pullDimes (p:=p) (N:=N) b (y N) s k U/(boardMass (C) N p k U:ℂ)∂Therm.scene H N p k) =
       moment ((C).beta N p) (fineJob (fun j=>abrade (C) (w j) N k p (x j) ht) s.val) := by
    have hp (U): (boardMass (C) N p k U:ℂ)≠0:= Complex.ofReal_ne_zero.mpr ((boardPos («C»:=C) R.makes N p ht U).ne')
    refine ⟨Envelope.compactC ((continuousDimes b (y N) s ht).div
      (Complex.continuous_ofReal.comp (boardContinuous («C»:=C) R.makes N p ht)) hp),?_⟩
    rw [Therm.violet («H»:=H) R.makes.wilson ht,
      ← rootSale R d w x ht]
    congr 1
    apply integral_congr_ae
    filter_upwards with U
    exact mul_div_cancel₀ _ (hp U) -- order

local notation "g"=> Pert.Asymptotics.regulatorRun R.family
local notation "X"=> R.family.path.levels.clock.hatBeta
variable {T0:Campaign R}{W:Campaign.Pillars R T0} {h:G.Simple}(U:Pier.Starter R h T0 W)
variable (c e t wide:ℕ)(hi:1≤wide)

abbrev gapTag (N:ℕ) (s:Γ.Mode)(x:Fin n→ Site (R.family.side k p)) (z:Fin n→ (C).book.Token)
    (U:Config G (R.family.side k p)) :=
    pullDimes z (p:=p) (N:=N) (attachV R k x N) s k U / (boardMass (C) N p k U : ℂ) -
          ∏ j∈ s.val, lines17 z (p:=p) (attachV R k x) N k j U

include U hi
/-
The arity, power and Aspect factor are fixed demands served by one Starter.
NO restrictions on tile count, arity of lower horizon where a previous stress
analysis might work, period or history length etc. Native mesoscopic
payment on every input before OPE conversion. Width exponent must admit
eligible distances. This lemma never supposes any points pass geometry unless
used by caller; eligible K purchase still has to pay test positions further.
-/
theorem allScenes :
    ∀ᶠ k:ℕ in atTop,∀ l:ℕ,(R.family.path.levels.budget k).B^8 ≤ l→ (l:ℝ) ≤ (X k)^t → ∀ N p:ℕ, k<N→
     ∀ x:Fin n→ Site (R.family.side k p), (∀ k j, separation (x k) (x j) ≤ wide*l) →
       (∀ k j,k≠j→ l ≤ separation (x k) (x j)) →
     ∀ v:(j:Fin n)→ R.family.label (d j), (∀ j, Spindle.paid (C) (d j) k N p (v j) ≤ (X k)^c) →
     ∀ s:Γ.Mode, Integrable (gapTag R N s x (recordS R d v)) (Therm.scene H N p k) ∧
       ‖∫ U,gapTag R N s x (recordS R d v) U∂(Therm.scene H N p k)‖ ≤
         2^e * (Pert.Asymptotics.regulatorRun R.family N p k)^(2*e) := by
    let K:ℕ×ℕ→ℕ:= Prod.fst; let n':ℕ×ℕ→ℕ:= Prod.snd
    let S:=(Filter.comap K atTop); let A : Set (ℕ×ℕ):={q | ((C).path.levels.budget (K q)).B^8≤ n' q ∧ (n' q:ℝ)≤ (X (K q))^t}
    let M:= S ⊓ Filter.principal A
    have hT:Tendsto K M atTop:= tendsto_iff_comap.mpr inf_le_left
    have hB:∀ᶠ i in M,i∈A:= Filter.Eventually.filter_mono (show M ≤ (Filter.principal A) from inf_le_right) ((eventually_principal).mpr (fun _ h=>h))
    have hw: Height (C).S M ((C).S.scale ∘ K) K 1:= ⟨hT,tendsto_const_nhds.congr' ((((C).S.divergent.comp hT).eventually_gt_atTop 0).mono fun i hi=>(div_self (a:= (C).S.scale (K i)) (ne_of_gt hi)).symm)⟩
    have hz:= (C).S.divergent.comp hT -- fix open syntax
    let σ := (C).S.scale ∘ K; have hp:= Loom.hat_price hz hw
    let v:ℕ×ℕ→ℝ:= fun i=> X (K i)^c; have hk:Loom.Coins M ((C).S.scale ∘ K) v:= Loom.Coins.power hp hz _
    let F i:= (X (K i)^e)⁻¹
    have hh:Loom.Coins M σ F:=Loom.Coins.inv (Loom.Coins.power hp hz e)
    have hF(z):0<X z:= zero_lt_one.trans ((T).fits.delayed z)
    have hs:Loom.Cheap M σ (fun i=> (n' i:ℝ)) := (Loom.Cheap.power hp.up hz t).norm_le (hB.mono fun i (hi:i∈A)=> (Real.norm_of_nonneg (Nat.cast_nonneg _)).trans_le (hi.2.trans (Real.le_norm_self _)))
    obtain ⟨χ,χ',hχ⟩:= OPE.Yarn.enroll U.thresholds.toSharper U.uv.actual h
    have hx:= columnLaw (d:=d) (T₀:=U.thresholds) hχ (show GracesP (C) M K n' from ⟨hT,hs,hB.mono fun i (hi:i∈A)=>hi.1⟩) hi hk (Eventually.of_forall fun i=> (one_le_pow₀ ((T).fits.delayed _|>.le) : 1≤v i)) hh (Eventually.of_forall (fun i=> inv_pos.mpr (pow_pos (hF _) e))) -- arg order
    rw [Filter.eventually_inf_principal] at hx
    obtain ⟨u₁,hu,hU⟩:= hx
    filter_upwards [hu, eventually_all.mpr (fun j=>eventually_ge_atTop (R.family.ref (d j))), eventually_gt_atTop (R.family.ref 0)] with i hc hK hA l hl hl' N p he x hX hD v hV s
    have hg(z): (lines17 (recordS R d v) (p:=p) (attachV R i x) N i z) = regularRead (C) (d z) i N p (v z) (x z):=rfl
    have hy := hU (show (i,l) ∈ K ⁻¹' u₁ from hc) ⟨hl,hl'⟩ N p he x hX hD v hV s.val
    let y'(U):=∏ j∈s.val, regularRead (C) (d j) i N p (v j) (x j) U
    obtain ⟨he',hθ⟩:= sceneRoot R d v x he.le s
    letI:= Therm.probability («H»:=H) (p:=p) (show (H).Selected from R.makes.wilson) he.le -- replace
    have hR:Integrable y' (Therm.scene H N p i):=(Envelope.prodC s.val (fun j=>regularRead (C) (d j) i N p (v j) (x j)) (fun j _=>(enamelCost hχ U.thresholds (x j) (hK j) hA he (v j) (hV j)).1)).integrableC _
    let z:= attachV R i x
    let a:= recordS R d v
    let f(U):= pullDimes a (p:=p) (N:=N) (z N) s i U/(boardMass (C) N p i U:ℂ)
    have hd: gapTag R N s x a=f-y':=rfl
    rw [hd]; refine ⟨(he'.integrableC _).sub hR,?_⟩
    simp_rw [Pi.sub_apply]; rw [integral_sub (f:=f) (by exact he'.integrableC _) hR]; unfold f a z; rw [hθ]
    refine hy.trans ?_
    rw [pow_mul, ← mul_pow]; change F (i,l) ≤ _; unfold F K; rw [← inv_pow]; exact pow_le_pow_left₀ (inv_pos.mpr (hF _)).le (payBand R (p:=p) he.le).2.2 _
end YM.RG17.Panoramic
