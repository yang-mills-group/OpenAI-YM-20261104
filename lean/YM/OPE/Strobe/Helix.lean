import YM.OPE.Strobe.Magnify
/-! # Charge ∆ at one slot and propagate to fixed-hall estimates. Asymptotic. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
local notation "B" => ((fun i=>(C.path.levels.budget i).B))
local notation "X" => (C.path.levels.clock.hatBeta)
variable {φ : Filter I} {k n:I→ℕ}{v w s:I→ℝ}(L: GracesP C φ k n)
local notation "d*" => B
local notation "loc" => (fun i=>C.S.scale (k i))
local notation "a" => (C.path.levels.clock.hatBeta ∘ k)
local notation "sp" => (fun i=>chapter C (k i) (n i))
local notation "κ" => (fun i=>Real.sqrt (C.path.levels.clock.forcedAllowance i))
include H L
local notation "J!" => (fun j=> (chapter C (k j) (n j)))
section
variable (b:ℕ)(hb:0<b)
include hb
private lemma pack {w:I→J→ℝ}(ht:∀ j,Coins φ (C.S.scale ∘ k) (fun i=>w i j))(hZ:Barrow C r m b z) (he:C.ref 0<z) : Coins φ (C.S.scale ∘ k) (fun i=>pound C b m z (J! i) (k i) (Mast.PatrolFee C J (J! i)) (w i)) := Function.const _ (Function.const _ (by
    let K:=k; let M:= (J!); have h:=footing H L (j:=M) rfl; have hx:= C.S.divergent.comp L.seeks; let q i:=Mast.PatrolFee C J (M i); let w' i:= shade C b (q i) (M i) (K i) false (w i); have hA : Coins φ loc w':=by
       have hu:= license_polynomial hx h.1 (Mast.spaces J) H.cuts hb; have hv:= Yarn.roam_bill (j:=M) (k:=k) (K:=false) H hx L.ages h.1 (fun _=>h.2.1.symm); simpa only [w',shade,cashIn,prod_const_one] using! Bi.prod (s:=Finset.univ) hx (fun j _=> Coins.mul hu (Coins.mul hv (ht j)))
    have hz:C.ref 0≤ z:= he.le; have he₀ : 0 < earns C m z := Real.exp_pos _; have hc:= Yarn.pitch_bill H hx h.1; have hr:0 < license P δ 1 1 z:= license_pos 1 1 (H.mantle hz).funs.1 Nat.one_pos; unfold pound; simp only [shade,cashIn,Fintype.prod_unique]; -- unfolds w' reducing.M.Correct
    exact Coins.div (Bi.const _ he₀.ne' hx) (Coins.mul (Bi.const _ hr.ne' hx) (Coins.mul hc hA))) hZ) (‹DecidableEq J›) -- Yarn. fee true reducible
private lemma closing' (hm:C.ref 0< z)(t j k l:ℕ)(hk:j < k)(hz:z < j)(x:J→ℝ)(hx:∀ j,0<x j) : 0 < pound C b t z j k l x:= Function.const _ (Function.const _ (by
   have hH(j k:ℕ)(hm:C.ref 0 ≤ j)(hk:j<k)(u:Bool)(l:ℕ)(r:J→ℝ)(hr:∀ i,0<r i) : 0 < shade C b l j k u r:= prod_pos fun i _=> mul_pos (license_pos b l (H.mantle hm).funs.1 hb) (mul_pos (Yarn.voucher H hk u|>.1) (hr i)); let v:= shade C b l j k false x; have hp:0<v := hH j k (hm.le.trans hz.le) hk _ _ _ hx; exact div_pos (Real.exp_pos _) (prod_pos fun i (_:i∈(univ:Finset Unit))=>mul_pos (license_pos 1 1 (H.mantle hm.le).funs.1 Nat.one_pos) (mul_pos (Yarn.voucher H hz true|>.1) hp))) L) (‹DecidableEq J›)
omit H L hb in
private lemma factorP {k j:ℕ}(l:ℕ)(p':J)(f:J→ℝ)(g:ℝ): pound C b m z j k l (Function.update f p' (g*f p')) = pound C b m z j k l f/g:=by
    let v:= Function.update f p' (g*f p'); let y t:= if t=p' then g else 1
    have hv : v=(fun t=>y t*f t) :=by
       funext i; by_cases h:i=p'
       · subst i; rw [show v p'= _ from Function.update_self ..]; unfold y; simp
       rw [show v i=f i from Function.update_of_ne h ..]; unfold y;rw [if_neg h,one_mul]
    let z':=license C.path δ b l j; let u:=Yarn.fee C j k false; let x:=shade C b l j k false f; have he : shade C b l j k false v=g*x:=by
       unfold x shade cashIn; rw [hv]; change ∏ i,z'*(u*(y i*f i)) = g*(∏ i,z'*(u*f i));  simp_rw [mul_left_comm u (y _), mul_left_comm z' (y _)] -- rw literal via change
       rw [prod_mul_distrib]; unfold y; simp
    change pound C b m z j k l v = _; unfold pound; rw [he]; unfold shade cashIn; simp only [Fintype.prod_unique]; -- unfolds RHS x or needed
    unfold x shade cashIn; simp_rw [div_eq_mul_inv,mul_inv_rev]; ring
end
-- no GracesP & etc closing binder optimize. compile edit
variable {x:I→ℝ} (ice:J→Bool)(i₀:J)(hm : Barrow C r m (Fintype.card J) z)(hz:C.ref 0< z)(d:ℕ)
local notation "b" => Fintype.card J
local notation "q" => (fun i=>Mast.PatrolFee C J (J! i))
local notation "w*" => (fun i=>payment C (k i) 0 (v i) false)
local notation "r*" i => (B (k i))
local notation "Q" i y => pound C (Fintype.card J) m z (J! i) (k i) (q i) (y)
include hm hz
lemma bounded_jobs (T₀:Citizen C W r D) (p':J) (hχ:ice p'=true)(hw:Coins φ (C.S.scale ∘ k) v)(hv:∀ᶠ i in φ,0<v i)(hs:Coins φ (C.S.scale ∘ k) s) (ht:∀ᶠ i in φ,0<s i): ∀ᶠ i in φ, ∀ N p,∀ he:k i < N,∀ x:J→Site (C.side (k i) p), Habits C (k i) p (n i) x i₀→∀ x₁:J→ C.label d, (∀ j, Spindle.paid C d (k i) N p (x₁ j) ≤ v i) → ‖moment (C.beta N p) (fineJob (fun j=> writeF C (x₁ j) N (k i) p (B (k i)) (x j) he.le (ice j)) univ)‖ ≤ s i:= by
    let w' i:= (w* i)⁻¹; let K i:= pound C b m z (J! i) (k i) (q i) (fun _ : J=> w' i); let y' i:=δ (k i); let U j i:= if j=p' then w' i * (K i / s i) else w' i; let S i:= ζ d (k i)/v i; have he:= C.S.divergent.comp L.seeks
    letI:Nonempty J:= ⟨i₀⟩; have hb:0<(Fintype.card J):=Fintype.card_pos; have hh:Coins φ loc w':= Coins.inv (modulo H L 0 hw hv); have hK:= pack (w:=fun i (_:J)=>w' i) H L b hb (fun i=> hh) hm hz; have hρ j:Coins φ loc (U j):= by unfold U; split; exact Coins.mul hh (Coins.div hK hs); exact hh
    have hS:Coins φ loc S:= Coins.div (fly_coins he L.ages d) hw; have h':∀ᶠ i in φ,0<S i:= hv.mono fun i hi=> div_pos (H.fog_mono d (le_refl (k i))|>.1) hi; obtain ⟨t,ht',hU⟩:= ((eventually_gt_atTop 0).and ((show ∀ᶠ t:ℕ in atTop,∀ j:J,∀ᶠ i in φ,U j i ≤ δ (k i)*(η (k i)* S i)*Real.exp ((Loom.count C t (k i):ℝ)/24) from eventually_all.mpr (fun j=> ruby H L hS (hρ j|>.up) h')))).exists
    let A i:= 2*((T).params (k i)).columns*(v i) * U p' i -- θ' missing
    have hA:= Cheap.mul (Cheap.mul (Cheap.mul (Bill.const (2:ℝ) he) (columns_p he H.cuts.toPackage.toTableTickets L.ages|>.up)) hw.up) (hρ p'|>.up); filter_upwards [hv,ht,bolted H L T₀ d t hm hz,eventually_all.mpr hU,stainBeat H L (v:=A) hA] with i hi hs h hp hh N p hn x hX x₁ hx
    have hw':0 < w* i:= (payday false 0 C (k i) hi).1; have hw:0<w' i:= inv_pos.mpr hw'; have he:0<K i:= closing' H L b hb hz m (J! i) (k i) (q i) h.next h.scroll _ (fun _=>hw); let w j:=U j i; have hV(j): 0<w j:=by unfold w U; split; exact mul_pos hw (div_pos he hs); exact hw
    apply le_trans (decayF H i₀ hX h le_rfl x₁ ice (v i) hn T₀ ht' hx (show 0<S i from div_pos (H.fog_mono d (Nat.le_refl (k i)) |>.1) hi) (by unfold S; rw [div_mul_cancel₀ _ hi.ne']) hV ?_ hp); swap
    · intro j; by_cases hc:j=p'
      · subst j; rw [hχ]; let R':=payment C (k i) (B (k i)) (v i) true; let l' := Real.exp (-2*(B (k i):ℝ)); have ht' : ‖A i‖=A i:= Real.norm_of_nonneg (show 0 ≤ A i from (by unfold A; have h0:0 < U p' i:=hV _; have hx:=((T).params (k i)).columns_ge; positivity)); rw [ht'] at hh; obtain ⟨hg,hg'⟩:= hh; rw [← mul_div_assoc, mul_one, le_div_iff₀ (hV p')]; change (2*_* (v i)*(l'+κ (k i)))*U p' i≤4; exact le_trans (le_of_eq (show _= A i*l'+A i*(κ (k i)) from by unfold A; ring)) (by linarith only [hg,hg'] )
      refine (payday (ice j) (B (k i)) _ _ hi|>.2).trans ?_; unfold w U; rw [if_neg hc,one_div]; unfold w'; rw [inv_inv]; linarith
    apply le_of_eq
    have hV: w= Function.update (fun _:J=>w' i) p' ((K i/s i)*w' i):=by ext v; by_cases h:v=p'; subst v; rw [Function.update_self]; unfold w U; rw [if_pos rfl,mul_comm]; rw [Function.update_of_ne h]; exact if_neg h
    rw [hV,factorP]; change K i/(K i/s i)= _; field_simp
end YM.OPE.Strobe

