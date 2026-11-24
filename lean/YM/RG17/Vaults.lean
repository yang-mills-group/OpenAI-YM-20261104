import YM.RG17.Drove
import YM.RG17.City
/-! Carrying to secular frame. ACTUAL post selectors included limits.
ValueStamp, at ANY inner price e.g. g^6. normalizes using liftVac nonzero
on chart (from honesty) and not partition estimate. Pre-cost of pulling
independent WilsonX power series to THESE tariffs still missing.
 Does not assume NearRent for such prediction. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open Extra.Multi FullVolume.Sever Marker Source Overlay PhysicalNext.Repeat.Mallow Bandage MergeProof MergeProof.Accent Ribbons ManyCopies Extra.Histories Extraction Word Next.Rank Station Edition Spindle Cells Table
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G){S:Table R.family.book}{f: Extraction.Order}
 {F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B} (Z:Ledger L) (fx:Flick R.family.path.levels)(W:Services R.family f S) (hz:Pegs D L)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "ν"=> Bid.gainChart R.family.path
local notation "o"=>home
local notation "T"=> OPE.run
open Push
variable (d:ℕ)
set_option quotPrecheck false
local notation "Θ"=> R.family.label d
local notation "I"=> (R.family.labels.level d).Index
abbrev ArchView (k p:ℕ):= {x: Space G (0:Site (R.family.side k p)) (sizeQ R.family k)// ‖x‖ ≤ (H k^6)⁻¹}
def watchman (k N p:ℕ)(y:R.family.label d) (x:ArchView R k p):ℂ:=awakeFull C k N p y (net (C|>.path.rep N p k|>.p) 0 (sizeQ C k) x.val)
structure ClockFace (k N p:ℕ) where
    tiles: (R.family.labels.level d).Index → ArchView R k p
    coinL: R.family.label d ≃ₗ[ℂ] ((R.family.labels.level d).Index→ℂ)
    register: ∀ v i, coinL v i = watchman R d k N p v (tiles i)
    tick:∀ x:ArchView R k p, IsLinearMap ℂ (fun v=>watchman R d k N p v x)
    modest:∀ v B, (∀ i, ‖watchman R d k N p v (tiles i)‖≤B)→∀ x, ‖watchman R d k N p v x‖≤2*(Fintype.card (R.family.labels.level d).Index)*B
include fx W
lemma clocksFaces: ∀ᶠ k in atTop, ∀ N p:ℕ,k≤N→ Nonempty (ClockFace R d k N p):=by
    have ho:∀ᶠ k in atTop, ((ι).params k).columns ≤ H k := (eventually_ge_atTop 1).mono fun _ hk=> possibleOdds R fx W hk
    filter_upwards [paidThrough C d R.makes W.simpleGate ho,eventually_ge_atTop (C|>.ref d)] with k hg hk N p hN
    let A:= (C|>.path.rep N p k); let b:=sizeQ C k
    let f (x:ArchView R k p)(y:Θ):= watchman R d k N p y x; have ht:=hg N p hN; obtain ⟨e,he⟩:∃ E:(ArchView R k p)→(Θ →ₗ[ℂ] ℂ),∀ x v,E x v=f x v:=by
       have hv(x): IsLinearMap ℂ (f x):=by
           have hl(v w s): f x (v+s • w)=f x v+s*f x w:= (on_branch R.makes hk hN p _ (ht.1 x.val x.property) v).2.2 w s
           have h':= hl 0 0 1; have h0:f x 0=0:=by simpa only [one_smul,add_zero,one_mul,left_eq_add] using h' -- zero simplification
           exact ⟨fun v w=>by simpa using hl v w 1,fun c v=>by simpa [h0] using hl 0 v c⟩
       exact ⟨fun x=> IsLinearMap.mk' _ (hv x),fun x v=>rfl⟩
    have hs: ∀ v,∃ B:ℝ,∀ x, ‖e x v‖≤B:=by
       intro v; let M:= parcel C d k N p v; have hv:M.remBound 0 A _ _:= (R.makes.calibrated d N p (hk.trans hN)).cap k hk hN _
       let z:=(C|>.path.levels.params k|>.columns); have hj:0≤z:=zero_le_one.trans ((C|>.path.levels.params k|>.columns_ge)); have hr:=R.makes.wilson.represents N p k hN|>.vac
       have he'(U:Config G (C|>.side k p)):= MergeProof.Accent.hull (R.family.localSection d) A 0 M U («C»:=z) (fun i=> by rw [show A.p=_ from hr]; exact R.makes.priced d k p hk 0 i) hv (divisor_le ..) hj
       refine ⟨‖pinHat C d k‖*((1+z)*(C|>.labels.level d|>.coeffSize M.x)+z*(C|>.labels.level d|>.coeffSize ((C|>.labels.level d|>.core M.x)))), fun i=>?_⟩; rw [he]; unfold f watchman awakeFull; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (he' _) (norm_nonneg _)
    have hX:∀ v, (∀ x, e x v=0)→ v=0:=by
       intro v hi; have hv : paid C d k N p v ≤ H k^(3+6*d)*0:= ht.2 _ _ fun x hx=> norm_le_zero_iff.mpr ((he ⟨x,hx⟩ v).symm.trans (hi _))
       rw [mul_zero] at hv
       have hq: quota C d k N p v = a k^d* paid C d k N p v:=by
           unfold Spindle.paid Price.awake; rw [Size.smul,norm_inv,norm_pow, Complex.norm_real, Real.norm_of_nonneg (R.family.S.a_pos _).le, ← mul_assoc, mul_inv_cancel₀ (pow_pos (R.family.S.a_pos _) _|>.ne'),one_mul]; rfl
       obtain ⟨c,hc,hP⟩:=quota_stop C R.makes hk; apply norm_le_zero_iff.mp; exact le_trans (hP N p v hN) (by rw [hq, le_antisymm hv (paid_pos ..),mul_zero,mul_zero])
    obtain ⟨y,S,hS,hU⟩:= voll («ι»:=I) e hX hs
    exact ⟨⟨y,S,fun v i=>(hS v i).trans (he ..),fun x=> show IsLinearMap ℂ (f x) by rw [show f x=e x from funext fun i=> (he x i).symm]; exact (e x).isLinear,fun v B hp x=> by rw [show watchman _ _ _ _ _ _ _ = _ from (he x v).symm]; exact hU _ _ (fun i=>(congr_arg norm (he (y i) v)).le.trans (hp i)) x⟩⟩
end YM.RG17
