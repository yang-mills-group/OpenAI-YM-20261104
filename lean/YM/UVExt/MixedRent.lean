import YM.UVExt.StrongRelay
import YM.Push.RELAY_DIFFERENCE.Placement
import YM.Cells.Proximity

/-!
# Jointly deploy bounded tile prices or erased microscopic expressions
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Slots
open Set Function MeasureTheory Filter Lattice Wilson RG Push Extraction Extraction.Lease RelayDifference
open Cells MergeProof
open Dash Bid
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order}
set_option quotPrecheck false
section Tiling
variable {n : Side}
lemma rotate_add (u v : Config G n→ℂ) (b : Bool) (s : Signed) (x : Site n) :
    oriented (u+v) b s x=oriented u b s x+ oriented v b s x := funext fun y=> by cases b <;> simp [RelayDifference.oriented,hand]
lemma rotate_neg (u : Config G n→ℂ) (b : Bool) (s : Signed) (x : Site n) :
    oriented (-u) b s x=-(oriented u b s x) := funext fun y=> by cases b <;> simp [RelayDifference.oriented,hand]
lemma literal_oriented (u : Config G n→ℂ) (b : Bool) (s : Signed) : literal (oriented u b s) := fun _ _ =>funext fun i=> by
  unfold RelayDifference.oriented Function.comp
  congr 2
  simp [← pull_one,pull_pull,affine]

def priceAt {T : Tiling n} (F : Config G n→ℂ) (J : ℕ) (β A : ℝ): Prop :=
    ∀ (x : Site n), x∈T.margin 0 (T.side.val/J) → ∀ (b:Bool) (s:Signed), diag s →
    Interior (T.chamber 0) (oriented F b s x) ∧ T.rootTest β (oriented F b s x) ≤ A
lemma priceAt.add {T : Tiling n} {F P : Config G n→ℂ} {J : ℕ} {β A B : ℝ} (hC : Seam G n β) (h : priceAt (T:=T) F J β A)
    (h' : priceAt (T:=T) P J β B) : priceAt (T:=T) (F+P) J β (A+B) := fun x hx b s hh => rotate_add .. ▸
      (show let p:=oriented F b s x; let q:= oriented P b s x; Interior (T.chamber 0) (p+q) ∧ T.rootTest β (p+q) ≤ _ from by
       intro p q; exact ⟨(h x hx b s hh).1.plus (h' x hx b s hh).1,le_trans (hC.semi T p q (h x hx b s hh).1 (h' x hx b s hh).1)
        (add_le_add (h x hx b s hh).2 (h' x hx b s hh).2)⟩)
lemma priceAt.neg {T : Tiling n} {F : Config G n→ℂ} {J : ℕ} {β A : ℝ} (h : priceAt (T:=T) F J β A) : priceAt (T:=T) (-F) J β A := by
  intro x hx b s hh
  rw [rotate_neg]; refine ⟨by rw [← neg_one_smul ℂ (RelayDifference.oriented _ _ _ _ : Config G n→ℂ)]; exact (h x hx b s hh).1.scale (-1),?_⟩
  rw [← unitsC]; exact (h x hx b s hh).2
end Tiling

def TiledCaps (C : Family G) (f : Extraction.Order) (F : Trial C) := ∀ m J:ℕ, 0<J → ∃ A:ℝ, 0≤A ∧ f.late fun N p =>
    ∃ h:m≤N, ∀ T : Tiling (C.side N p), T.side.val=Cells.span C.S h p → T.kind=Kind.link → priceAt (F N p 0) (T:=T) J (C.beta N p) A

def CenterCaps (C : Family G) (f : Extraction.Order) (F : Trial C) := ∀ m₀:ℕ,∃ k : ℕ, m₀ ≤ k ∧ ∃ A : ℝ, 0≤A ∧ f.late fun N p=>
    ∃ h:k≤N, Interior ((center C.S p h 0).chamber 0) (F N p 0) ∧ (center C.S p h 0).rootTest (C.beta N p) (F N p 0) ≤ A
variable {F P : Trial C}
lemma CenterCaps.offset (H : CenterCaps C f F) (hC : C.Makes) : TiledCaps C f F := by
  intro m J hJ
  have hw : ∀ᶠ k in atTop, (3*J:ℕ)*C.S.a k ≤ C.S.a m := (C.S.shrinks.const_mul ((3*J:ℕ):ℝ)).eventually
      (ge_mem_nhds (show (↑(3*J:ℕ):ℝ) * 0 < C.S.a m from (mul_zero _).trans_lt (C.S.a_pos _)))
  obtain ⟨m₀,h₀⟩:= eventually_atTop.mp ((eventually_ge_atTop m).and hw)
  obtain ⟨k,hk,A,hA,he⟩:=H m₀
  obtain ⟨hr,hS⟩ := h₀ k hk
  refine ⟨A,hA,he.mono (fun p hp=> hp.mono fun N h=> ?_)⟩
  obtain ⟨hm,hw,hb⟩ := h
  refine ⟨(hr.trans hm),fun T he hY x hx b s hD=> ?_⟩
  let V:=f.mesh N; let a:= f.per p
  let t:=Cells.span C.S hm a; let Y:=F V a 0
  have ht : C.S.a V * t = C.S.a k := C.S.embeds_scale (C.S.toDepth hm a)
  have hR : C.S.a V * T.side.val = C.S.a m := he ▸ C.S.embeds_scale (C.S.toDepth (hr.trans hm) a)
  have hs : 3*t ≤ T.side.val/J := by
      apply (Nat.le_div_iff_mul_le hJ).2
      apply (Nat.cast_le (α:=ℝ)).1
      apply le_of_mul_le_mul_left _ (C.S.a_pos V)
      rw [hR]; rw [←ht] at hS; push_cast at *; linarith only [hS]
  refine RelayDifference.offset hm T (C.beta V a) A (he.symm ▸ Around.inherits hr hm) (literal_oriented Y b s)
    (seamless hC V a) (center_interior hm s hD b 0 hw) ((center_price hm 0 Y _ _ hD hw _).le.trans hb) (Lease.fewer T 0 hs hx)

lemma from_close (hC : C.Makes) (he : Bid.close C f F) : TiledCaps C f F := by
  apply CenterCaps.offset ?_ hC
  obtain ⟨y,hy,hr⟩ := he
  intro i
  obtain ⟨k,hk,H⟩:= hr 1 i
  have hb := (Order.fused f _).1 (hy.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)))
  refine ⟨k,hk,1,zero_le_one,(H.and hb).mono (fun j hi=> (hi.1.and hi.2).mono fun l hl=>?_)⟩
  obtain ⟨hq,hP⟩ := hl.1
  let T:= center C.S (f.per j) hq 0
  have ht := hP T rfl rfl 0 (Lease.fewer T 0 (Nat.div_le_div_left (by decide) (by decide)) (Stock.centered_margin ..))
  exact ⟨hq,ht.1,ht.2.trans hl.2⟩

lemma from_tight (hC : C.Makes) (H : CenterPort C f) {d : ℕ} {x : Rowe C d} (hx : tight C f x) :
    TiledCaps C f (upper C x) := by
  apply CenterCaps.offset ?_ hC; intro i
  obtain ⟨D,hD⟩:= hx
  obtain ⟨h,h',A,hA,hT⟩:= H.cells.centered d 1 (max 1 D) (by norm_num) (zero_lt_one.trans_le (le_max_left ..))
  have hw := hD.and (hT (max i h) (le_max_right ..) 1 (by norm_num))
  refine ⟨max i h,le_max_left ..,A*C.S.a (max i h)^(-(d:ℝ)-(1:ℝ))+1,(by apply add_nonneg (mul_nonneg hA (by exact Real.rpow_nonneg (Schedule.a_pos C.S (max i h)).le _)) zero_le_one),
    hw.mono (fun p hp=> (hp.1.and hp.2).mono fun N h=>?_)⟩
  obtain ⟨hm,hP⟩ := h.2; exact ⟨hm,hP _ (h.1.trans (le_max_right ..)) 0⟩

lemma TiledCaps.add (hC : C.Makes) (h : TiledCaps C f F) (h' : TiledCaps C f P) : TiledCaps C f (F + P) := by
  intro m J hJ; obtain ⟨A,hA,H⟩:= h m J hJ; obtain ⟨B,hB,H'⟩:=h' m J hJ
  exact ⟨A+B,add_nonneg hA hB,(H.and H').mono fun p hp=> (hp.1.and hp.2).mono fun N hn=>
    ⟨hn.1.choose,fun T ht hY=> priceAt.add (seamless hC ..) (hn.1.choose_spec T ht hY) (hn.2.choose_spec T ht hY)⟩⟩
lemma TiledCaps.neg (h : TiledCaps C f F) : TiledCaps C f (-F) := by
  intro m J hJ; obtain ⟨A,hA,H⟩:= h m J hJ
  exact ⟨A,hA, H.mono fun p hp=> hp.mono fun N hn=> ⟨hn.choose,fun T ht hY=> priceAt.neg (hn.choose_spec T ht hY)⟩⟩
lemma TiledCaps.sub (hC : C.Makes) (h : TiledCaps C f F) (h' : TiledCaps C f P) : TiledCaps C f (F-P) := by rw [sub_eq_add_neg]; exact h.add hC h'.neg

def probes (N p n : ℕ) (F : Fin n→Trial C) (x : Fin n→Site (C.side N p)) :=
  moment (C.beta N p) (fun U=> ∏ i, F i N p (x i) U)
theorem packing (hC : C.Makes) {n : ℕ} (F : Fin n → Trial C) (h : ∀ i, Stencilled f (F i) ∧ TiledCaps C f (F i))
    {δ:ℝ} (hδ:0<δ) : ∃ A : ℝ,0≤A ∧ f.late fun N p=>∀ x : Fin n→Site (C.side N p),
    (∀ i j,i≠j → δ ≤ C.S.a N * separation (x i) (x j)) → ‖probes N p n F x‖ ≤ A := by
  obtain ⟨m,hm⟩ := (C.S.shrinks.eventually (gt_mem_nhds hδ)).exists
  let J:=8*(n+1); have hJ : 0<J:=by unfold J; omega
  choose A hA H using fun i=> (h i).2 m J hJ
  have ht := (Order.fused f _).1 (eventually_all.mpr (fun i=>(h i).1.literal))
  refine ⟨∏ i,A i, Finset.prod_nonneg fun i _=> hA i,?_⟩
  unfold Order.late at H ht ⊢
  filter_upwards [eventually_all.mpr H,ht] with p hp hh
  filter_upwards [eventually_all.mpr hp,hh,f.mesh.cofinal.eventually (eventually_ge_atTop m),
    (C.S.shrinks.comp f.mesh.cofinal|>.eventually (gt_mem_nhds (b:=0) (a:=C.S.a m/(J:ℝ)) (div_pos (C.S.a_pos m) (Nat.cast_pos.mpr hJ))))] with N hn hf hM hNa x hx
  · let n':=f.mesh N; let p':=f.per p; let T:= center C.S p' hM 0
    let L := T.side.val
    have hS : C.S.a n'*L=C.S.a m:= trueLength ..
    have hL : J ≤ L := by
      exact_mod_cast (le_of_mul_le_mul_left (b:=(J:ℝ)) (c:=(L:ℝ)) (a:=C.S.a n') (by rw [hS]; exact ((lt_div_iff₀ (Nat.cast_pos.mpr hJ)).mp hNa).le) (C.S.a_pos _))
    have hP : n*(2*(L/J)) < L := by
      have hP := Nat.mul_div_le L J
      have ht : 2*n < J := by dsimp [J]; omega
      nlinarith
    obtain ⟨j,hj⟩:= T.fits_together x (L/J) (Nat.div_pos hL hJ) hP
    let V:=T.newly j; let g (i:Fin n):=V.which (x i)
    have hc : Function.Injective g:= by
      intro i k h'; by_contra h₀
      have hp := V.extent (hj i|>.1) (show x k∈V.chamber (g i) from h' ▸ (hj k).1)
      exact hm.not_ge ((hx i k h₀).trans ((mul_le_mul_of_nonneg_left (show (separation (x i) (x k):ℝ) ≤ L by exact_mod_cast hp) (C.S.a_pos _).le).trans_eq hS))
    choose y hy using fun i=>V.pointed (g i) (x i)
    let s (i:Fin n) := (V.omega (g i))⁻¹; let b(i : Fin n) := decide (V.hand (g i))
    have hd i : diag (s i) := diag_inv (by rfl)
    let U i := oriented (F i n' p' 0) (b i) (s i) (y i)
    have hw i : V.copy (g i) (U i) = F i n' p' (x i) := by
      unfold U s; rw [copied,mul_inv_cancel,hy,show (decide _ ^^ b i)=false from Bool.xor_self _]; exact (unorient (hf i) _).symm
    have he i := (hn i).choose_spec V (by rfl) (by rfl) _ ((V.reflected_margin (y i) (g i) _).2 ?min) (b i) (s i) (hd i)
    refine le_trans (b:= ‖moment (C.beta n' p') (fun U'=>∏ i, V.copy (g i) (U i) U')‖) ?_
      ((V.planted (seamless hC ..) g hc U fun i=>(he i).1).trans (Finset.prod_le_prod (fun i _=> V.root_nonneg ..) (fun i _=> (he i).2)))
    unfold probes; simp_rw [hw]; rfl
    case min => rw [hy]; exact hj _
section Erase
private lemma bounds_local (s : Finset Cover) : ∃ r : ℕ,∀ᶠ N in atTop, ∀ p:ℕ,∀ z∈s,pdist (wrap (C.side N p) z) ≤ r:=by
   choose r M h using fun (i:Cover)=> Mark.place_size i
   let r₀ := s.sup r; refine ⟨r₀,?_⟩
   filter_upwards [(eventually_all_finset _).2 fun i (_:i∈s)=> Mark.lengths C.S (M i)] with N hh p x hx
   exact ((h x (C.side N p) (hh x hx p)).2).trans (Finset.le_sup hx)
theorem erase_manifest {n : ℕ} (hC : C.Makes) (F : Fin n→Trial C) (h : ∀ b, Stencilled f (F b)) (i : Fin n) (he : manifest (F i))
    {δ:ℝ} (hδ:0<δ) : f.late fun N p=>∀ x:Fin n→Site (C.side N p), (∀ j≠i,δ≤ C.S.a N * separation (x j) (x i)) → probes N p n F x=0:=by
    choose s hs using h
    choose r hr using fun j=> bounds_local (C:=C) (s j)
    obtain ⟨k,M,H⟩:= he
    have hd(j:Fin n) : ∀ᶠ N in atTop, C.S.a N*(k+r j)<δ := (C.S.shrinks.mul_const _).eventually (gt_mem_nhds (by simpa only [zero_mul] using hδ))
    apply Order.fused f (fun a=>∀ x:Fin n→Site (C.side a.1 a.2), (∀ j≠i,δ≤ C.S.a a.1 * separation (x j) (x i)) → probes a.1 a.2 n F x=0)|>.mp
    filter_upwards [eventually_all.mpr hs,(cutoff_grows f).eventually (eventually_all.mpr hr),(cutoff_grows f).eventually (eventually_all.mpr hd),
      (cutoff_grows f).eventually (Mark.lengths C.S M)] with a ha hx hq hM x hv
    obtain ⟨z,-,hz,ho⟩:=H a.1 a.2
    let K := Finset.univ.erase i; let T:= fun V => ∏ j∈K,(F j a.1 a.2 (x j) V)
    have hβ := Overlay.beta_positive hC.wilson (m:=a.1) (N:=a.1) (p:=a.2) le_rfl
    have hb j:= (ha j).fits (x j)
    calc
      _ = moment (C.beta a.1 a.2) (fun U=> z (expandAt (x i) U)*T U) := by
        unfold probes T; congr 1; funext u; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),ho]
      _ = 0:= hz _ (hM a.2) (x i) _ (by exact hβ.ne') T ?_ (Envelope.prodC _ _ (fun j _=> ⟨(hb j).borel,(hb j).cost⟩))
    · intro U W hW; refine Finset.prod_congr rfl (fun j hj=> (hb j).localSites U W (agrees_mono hW (fun y hy => ?_)))
      have hh : k+r j < separation (x j) (x i):=by exact_mod_cast (lt_of_mul_lt_mul_left ((hq j).trans_le (hv j (Finset.ne_of_mem_erase hj))) (C.S.a_pos a.1).le)
      obtain ⟨v,hv,rfl⟩:= Finset.mem_image.mp hy; replace hx:= hx j a.2 v hv
      set W0:= wrap (C.side a.1 a.2) v+x j
      have hp:= separation_triangle (x j) W0 (x i)
      rw [separation_comm (x j) W0, show separation W0 (x j)=pdist (W0-x j) from rfl,show W0-x j=wrap _ v from add_sub_cancel_right ..] at hp
      change k < _; omega
end Erase
end YM.UVExt.Slots
