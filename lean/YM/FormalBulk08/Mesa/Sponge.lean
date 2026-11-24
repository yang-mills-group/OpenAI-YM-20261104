import YM.FormalBulk08.Shore.Crown

/-! Fold as linear cover sum, common anchor geometry. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Mesa
open Lava Gorge Shore Lattice Laurent Filter Function Lotus
open scoped Topology ENNReal BigOperators Classical
variable {V I : Type*} {r : ℕ} (i : Fin r) (n : Side)

lemma lights_unique {T U : Tile (Biglot I) r} {R : (n:Side)→ Tile (Tor n I) r} (h : Light T R) (e : Light U R) : T=U:= funext fun v=>tendsto_nhds_unique (h v) (e _)
lemma light_agate {T : Tile (Biglot I) r} {P : (n:Side) → Tile (Tor n I) r} (h : Light T P) (e : ∀ᶠ n in atTop, Agate (P n)) : Agate T:= by
   intro v s; apply tendsto_nhds_unique (h (v ∘ s))
   exact (h v).congr' (e.mono fun n hn=> (hn (drip n ∘ v) s).symm)
lemma light_up {T : Tile (Biglot I) r} {P : (n:Side) → Tile (Tor n I) r} (h : Light T P) (e : ∀ᶠ n in atTop, Up (P n)) : Up T:= by
   intro c v; apply tendsto_nhds_unique (h (tint c ∘ v)); apply (h v).congr'
   filter_upwards [e] with n hn; rw [show drip n ∘ tint c ∘ v= tint (wrap n c) ∘ (drip n ∘ v) from funext fun j=> drip_tint ..]; exact (hn _ _).symm
lemma up_zero {C : Type*} [AddCommGroup C] (r : ℕ) : Up (0 : Tile (C×I) r):=fun _ _=>rfl
lemma cum_zero : cum i n (0 : Tile (Biglot I) r)=0 := by funext; simp [cum,vat]
lemma funds_vat {T : Tile (Biglot I) r} {v : chain (Tor n I) r} {σ C : ℝ} (hs : 0≤σ) (h : Bail (fame I) σ T C) (x : Biglot I) : Summable fun w:Picks i n x v=> T w.val := by
   let f : Picks i n x v → pack i x:= fun w=>⟨w.val,w.property.1⟩
   exact (glitter_sum_usable h hs i x).comp_injective (show Injective f from fun _ _ e=>Subtype.ext (congr_arg (fun w:pack i x=>w.val) e)) -- requires real abs
lemma cum_plus {T U : Tile (Biglot I) r} {σ ξ C A : ℝ} (hs : 0≤σ) (hx : 0≤ξ) (h : Bail (fame I) σ T C) (a : Bail (fame I) ξ U A) : cum i n (T+U)=cum i n T+cum i n U := by
   funext; exact (funds_vat i n hs h _).tsum_add (funds_vat i n hx a _)
lemma cum_smul (T : Tile (Biglot I) r) (b : ℝ) : cum i n (b • T)=b • cum i n T := by funext v; exact tsum_mul_left .. -- total field
lemma cum_spin {T : Tile (Biglot I) r} (s : Equiv.Perm (Fin r)) (h : Up T) :
    cum i n (fun v=> T (v ∘ s)) = (fun v=> cum i n T (v ∘ s)) := by
   funext v; rw [cum_root i (s.symm i) n _ T h]
   let W:=v∘s; let x:= boil n (v i); let F:= cum (s.symm i) n T
   have he : drip n x=W (s.symm i):=by simp [x,W]
   change _= cum _ n T W
   rw [cum_near _ n h W x he]; unfold vat cum; unfold vat
   let S:=Picks i n x v; let Y:= Picks (s.symm i) n x W
   let e : S≃ Y:=⟨fun w=> ⟨w.val ∘ s,by simp [w.property.1],funext fun j=>congr_fun w.property.2 (s j)⟩, fun w=> ⟨w.val ∘ s.symm,w.property.1,funext fun j=>by have hh:=congr_fun w.property.2 (s.symm j); simpa [W] using hh⟩,fun w=>Subtype.ext (funext fun j=>by simp), fun w=>Subtype.ext (funext fun j=>by simp)⟩
   exact e.tsum_eq (fun w=> T w.val)
lemma cum_sums (t:Finset V) (T:V→Tile (Biglot I) r) {σ : ℝ} {C : V → ℝ} (h : ∀ j∈t,Bail (fame I) σ (T j) (C j)) (hs : 0 ≤ σ) : cum i n (∑ j∈t,T j)=∑ j∈t,cum i n (T j) := by
   induction t using Finset.induction with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty,cum_zero]
   | @insert a t he ih=>
      have ht (j:V)(h':j∈t) := h j (Finset.mem_insert_of_mem h')
      rw [Finset.sum_insert he,Finset.sum_insert he,cum_plus i n hs hs (h _ (Finset.mem_insert_self a t)) (bail_many _ _ C ht),ih ht]
lemma up_sums {H : Type*} [AddCommGroup H] (t:Finset V) (T : V→ Tile (H × I) r) (h : ∀ j∈t, Up (T j)) : Up (∑ j∈t,T j) := by
   intro x v; simp_rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=> h i hi _ _
lemma up_spins {H : Type*} [AddCommGroup H] {T : Tile (H×I) r} (h : Up T) (s : Equiv.Perm (Fin r)) : Up (fun v=>T (v ∘ s)):= fun x v=> h x (v ∘ s)
lemma up_smooth {H : Type*} [AddCommGroup H] {T : Tile (H×I) r} (h : Up T) : Up (sand T) := by
   intro x v; unfold sand; congr 1; exact Finset.sum_congr rfl fun s _=>up_spins h s x v
lemma cum_sand {T : Tile (Biglot I) r} {σ C : ℝ} (hs : 0 ≤ σ) (h : Bail (fame I) σ T C) (a : Up T) : cum i n (sand T)= sand (cum i n T) := by
   let d:=Fintype.card (Equiv.Perm (Fin r))
   have he : sand T = ∑ s: Equiv.Perm (Fin r),(d:ℝ)⁻¹ • (fun v:chain _ r=>T (v ∘ s)):= by funext; simp only [sand,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,d]; rw [←Finset.mul_sum,mul_comm]
   rw [he,cum_sums i n _ _ (fun s _=>(h.spins s).smul _) hs]; simp_rw [cum_smul,cum_spin i n _ a]; funext; simp only [sand,Finset.sum_apply, Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,d]; rw [←Finset.mul_sum,mul_comm]
end YM.FormalBulk08.Mesa
