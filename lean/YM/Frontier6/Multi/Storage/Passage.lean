import YM.Frontier6.Multi.Storage.Leaders
import YM.Frontier6.Multi.Scene.Flank

/- Sweeping state over variable-arity copies on actual support prog. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V C O:Type}[Fintype V][DecidableEq V][Fintype O][DecidableEq O][Fintype C][DecidableEq C]
variable {G:Gauge}
section germs
variable (H:History G)(δ:ℕ→ℝ)(r:ℕ→ℕ)
   (D:∀ N p i,i < N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
variable {N p i:ℕ}(σ χ:ℕ→ℝ)(v:V) (P:V→Motion)(B:V→Equiv.Perm V)
   (E:∀ i:ℕ,V→Site (H.S.side i p))(o:∀ i:ℕ,Live V O→Site (H.S.side i p))
set_option quotPrecheck false
local notation "X"=> (Now V O)
local notation "P'"=> H.levels.budget
local notation "R"=> H.rep N p
structure Atlas (δ χ:ℕ→ℝ)(i:ℕ){N:ℕ}(F:Config G (H.S.side i p)→Poly (Now V O))(w:O→ℝ) : Prop where
    sells : ∃ (g:Live V O→ Config G (H.S.side i p)→ℂ)(k:Live V O→ℕ→ Config G (H.S.side i p)→ℂ) (l:Live V O→ℂ),
        Arc (H.rep N p i) g k F v P (E i) B (o i) (fun j=> w j.2) ((H.levels.budget i).supportExponent+1/2) ((H.levels.budget i).supportExponent+1) 1 (χ i) (δ i) l ∧ (∀ j, w j.2*‖l j‖ ≤ 1) ∧ (∀ x : V,x≠v→∀ b:O,l (x,b)=scalar (P x) (l (v,b)))

structure Parcels (i:ℕ){N:ℕ}(F:Config G (H.S.side i p)→Poly (Now V O))(w:O→ℝ) (l:Live V O→ℂ) : Prop where
    shop : ∃ (g:Live V O→ Config G (H.S.side i p)→ℂ)(k:Live V O→ℕ→ Config G (H.S.side i p)→ℂ),
        Serves (H.rep N p i) g (fun j=>profile (H.rep N p i).activities (k j)) F v P (E i) B (o i) (fun j=> w j.2) ((H.levels.budget i).supportExponent) 1 ∧ May v P (E i) B g (fun j=>profile (H.rep N p i).activities (k j)) l ∧
        (∀ j:Live V O,Dominated (k j))∧(∀ j:O,Blade (H.rep N p i) (o i (v,j)) (g (v,j)) (profile (H.rep N p i).activities (k (v,j))) (l (v,j)) (1/(2*w j)))
structure Stores (i:ℕ){N:ℕ}(F:Config G (H.S.side i p)→Poly (Now V O))(w:O→ℝ) : Prop where
    pay : ∀ j,0<w j
    fits : ∃ l:Live V O→ℂ, Parcels H v P B E o i (N:=N) F w l ∧ ∀ j:Live V O,w j.2*‖l j‖ ≤ 1
-- parameter order actual H explicit
variable (h:H.Selected)(μ:ℕ)(hr:Thor H δ r D σ χ μ)
local notation "T"=> (H.levels.clock.op i p)
local notation "atlas"=>Atlas H v P B E o
local notation "shops"=>Stores H v P B E o
variable (w:O→ℝ)
include h hr
local notation "A"=>P' i
local notation "J"=> (A).B
local notation "cut"=> (4* (J^2)+1)

def pinion (S:Schedule)(i:ℕ)(w:O→ℝ)(b:O):= w b * (S.a (i+1)/S.a i)^4
omit h hr in
lemma pinion_age (S:Schedule)(i:ℕ): S.a (i+1) ≤ S.a i:= by rw [S.a_step]; exact div_le_self (S.a_pos i).le (by exact_mod_cast (S.block i).property)
local notation "w!"=>fun j:O=> δ i * w j
lemma onward {F:Config G (H.S.side (i+1) p)→Poly (Now V O)}(ht:μ ≤ i)(hN:i<N)(hX:Stores H v P B E o (i+1) (N:=N) F w)
    (hi:Integrable F (prior G _))(hx:Runs (D N p i hN) (H.levels.clock.op i p) (6*((H.S.block i).val:ℝ)))
    (he:(H.levels.clock.op i p).ratio.embed ∘ E i=E (i+1))(hy : Shaped v P (E (i+1)) (o (i+1)))
    (hO: (H.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i) (hs:Occupancy (o i) (r i))(hd:Occupancy (o (i+1)) (r i))
    (hg:1 ≤ δ i * mintK (H.levels.budget i).B)(hK:8 ≤ (H.levels.budget i).B) :
    let F' := (H.levels.clock.op i p).push (H.rep N p (i+1)|>.beta) F
    Atlas H v P B E o δ χ i (N:=N) F' (fun j=>δ i*w j) ∧ (Drake (Now V O) (H.levels.budget i).B (o i) → Stores H v P B E o i (N:=N) F' (pinion H.S i w)):=by
    intro F'; obtain ⟨hw,l,⟨g,k,hR,hM,hL,hV⟩,hp⟩:= hX; have ha:= hr.suns i ht; obtain ⟨hF,hF'⟩:= hr.moon N p i ht hN
    let L:ℝ:= (H.S.block i).val; have hE:E (i+1)=(fun j=>(T).ratio.embed (E i j)):=he.symm
    have hv(j:Live V O):2*w j.2*(1/(2*w j.snd)) ≤1:= by rw [mul_div_cancel₀ _ (by have he:=hw j.snd; positivity)];
    obtain ⟨G',u,h₀,h₁,h₂,h₃,h₄⟩:= flaring H r h hN ha hF hF' (fun j=> hw j.2) (hE ▸ hR) (by linarith only) hd (hO.symm ▸ hs) (fun _ _ _=>rfl) (fun j he b=> by rw [show _= E (i+1) j from (congr_fun hE j).symm]; exact hy j he b) (hE ▸ hM) hL hV hv hx (by positivity) hi
    have hw'(j):0 < w! j:= mul_pos ha.hats.1 (hw j)
    have hB : Drake X (J) (o i)→ Repegs (o i) (J) (fun j=> w! j.snd) (fun j=> pinion H.S i w j.snd) (1/2) 1 X:= ?_
    swap
    · intro hd; apply hd.palms _ (fun j=>by unfold pinion; exact mul_pos (hw _) (pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _)) (fun j=>hw' _) hK; intro j
      unfold pinion; calc
         _ ≤ w j.snd:=mul_le_of_le_one_right (hw _|>.le) (pow_le_one₀ (div_nonneg (H.S.a_pos _).le (H.S.a_pos _).le) ((div_le_one (H.S.a_pos _)).2 (pinion_age H.S i)))
         _ ≤ w j.snd*(δ i* mintK (P' i).B):= le_mul_of_one_le_right (hw _|>.le) hg
         _ = _ := by ring
    constructor
    · refine ⟨G',u,l,hO ▸ h₄,fun j=>?_,fun x hx b=> (hM _ hx).2 b|>.2.2⟩
      exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hw _|>.le) ha.hats.2) (norm_nonneg _)).trans (hp j)
    intro hΔ; have hw''(b):0 < pinion H.S i w b:=mul_pos (hw _) (pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _)
    have hz:= descended H N i p r h hN ha (I:=fun j=> w j.2) (fun j=>hw j.snd) (fun j : Live V O=>hw'' j.2) (hO.symm ▸ hs) (hO.symm ▸ hB hΔ) h₄ h₀ h₁
    rw [hO] at hz h₃
    refine ⟨hw'', l, ⟨G',u,hz,h₂,h₀,fun j=>?_⟩,fun j=>?_⟩
    · apply (h₃ j).more
      change 6*L*(1/(2*w j)) ≤ _; rw [← mul_div_assoc]; apply (div_le_div_iff₀ (mul_pos zero_lt_two (hw j)) (mul_pos zero_lt_two (hw'' j))).mpr
      have hL: 2 ≤ L:=by unfold L; exact_mod_cast ((le_trans (by norm_num) (H.S.block_large i)):2 ≤ (H.S.block i).val)
      have he: 8 ≤ L^3:=by have hz:= pow_le_pow_left₀ zero_le_two hL 3; norm_num at hz; exact hz
      have hp : L^4*pinion H.S i w j=w j:=by unfold pinion; rw [H.S.a_step]; change _*(w _*(H.S.a i / L/_)^4)=_; have hv:= H.S.a_pos i; have hi:0<L:=lt_of_lt_of_le zero_lt_two hL; field_simp
      nlinarith only [hp,he,mul_le_mul_of_nonneg_right he (mul_nonneg (show 0≤L from le_trans zero_le_two hL) (hw'' j).le), hL, hw'' j, mul_nonneg ((show 0 ≤ L from le_trans zero_le_two hL)) (hw'' j).le]
    exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hw _|>.le) (pow_le_one₀ (div_nonneg (H.S.a_pos _).le (H.S.a_pos _).le) ((div_le_one (H.S.a_pos _)).2 (pinion_age H.S i)))) (norm_nonneg _)).trans (hp j)
end germs
end YM.MergeProof.Canopies
