import YM.FormalBulk08.North.Nest

/-!
Dictionary between translation kernels and Laurent pictures at fixed rank.
All width choices in this library are BEFORE L, width measured absolutely
in the mesh of the expansion. These operations take place on aggregated
coefficients, not on masked histories.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior
open Reef Lava Gorge Mesa Shore Lotus Wick Series Jets
open Stationary hiding shine Rays
open scoped Topology ENNReal BigOperators Classical
variable {I:Type}{G:Gauge}{t:ℕ}{A σ:ℝ}

def packSlot (x:chain I (t+1))(p:Shift (Keys t)): chain (Biglot I) (t+1):= fun i=> (Fin.cons (α:=fun _=>Cover) 0 (fun j a=> p (j,a)) i,x i)
def arcSlot (x: chain (Biglot I) (t+1)) : Shift (Keys t):= fun u=>(x u.1.succ).1 u.2-(x 0).1 u.2
def arcType (x:chain (Biglot I) (t+1)): chain I (t+1):= Prod.snd ∘ x
@[simp] lemma pack_first (x:chain I (t+1))(p:Shift (Keys t)): packSlot x p 0=(0,x 0):=rfl
@[simp] lemma pack_after (x:chain I (t+1))(p:Shift (Keys t))(i): packSlot x p i.succ=(fun a=>p (i,a),x i.succ):= rfl
lemma pack_length (v : chain (Biglot I) (t+1)): size (arcSlot v)=∑ i:Fin t,(fame _).d (v i.succ) (v 0):= by
   unfold Laurent.size; rw [Fintype.sum_prod_type];rfl
lemma pack_extent (v: chain (Biglot I) (t+1)): size (arcSlot v)≤(t+1)*wide (fame _) v:= by
   rw [pack_length]
   refine le_trans (Finset.sum_le_sum (show ∀ j: Fin t,j∈Finset.univ → (fame I).d (v j.succ) (v 0) ≤ wide (fame _) v from fun j _=> reached ..)) ?_; simp [add_mul]
lemma pack_refine (v: chain (Biglot I) (t+1)): wide (fame _) v≤2*size (arcSlot v):= by
   have he (i:Fin (t+1)) : (fame I).d (v i) (v 0)≤size (arcSlot v):= by
      induction i using Fin.cases
      · rw [(fame I).self]; exact Nat.zero_le _
      next i=> rw [pack_length];exact Finset.single_le_sum (f:=fun i:Fin t=>(fame _).d (v i.succ) (v 0)) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)
   refine known_wide (fame _) _ _ fun i j=>?_ ; rw [two_mul]; have hh:= (fame I).tri (v i) (v 0) (v j);rw [(fame I).turn (v 0)] at hh; exact hh.trans (Nat.add_le_add (he i) (he j))
@[simp] lemma pack_shift (x:chain I (t+1))(p:Shift (Keys t)): arcSlot (packSlot x p)=p:= by ext ⟨i,j⟩; simp [arcSlot]
@[simp] lemma pack_ship (x:chain I (t+1))(p:Shift (Keys t)): arcType (packSlot x p)=x:=rfl
lemma pack_back (x:chain (Biglot I) (t+1)): tint ((x 0).1) ∘ packSlot (arcType x) (arcSlot x)=x:= by
   funext j; induction j using Fin.cases
   · refine Prod.ext ?_ rfl; simp
   next i=> refine Prod.ext ?_ rfl;ext a;simp [arcSlot,Lotus.tint]
lemma pack_unique (i : Fin (t+1))(p : Biglot I) : Injective (fun v:pack i p=>(arcType v.val,arcSlot v.val)):= by
    intro x y h;apply Subtype.ext
    obtain ⟨a,b⟩:=Prod.mk.inj h
    have he := pack_back x.val;rw [a,b] at he
    have hh : (x.val 0).1=(y.val 0).1:= add_left_cancel ((congr_arg Prod.fst (congr_fun he i)).trans ((congr_arg Prod.fst (x.property.trans y.property.symm)).trans (congr_arg Prod.fst (congr_fun (pack_back y.val) i)).symm))
    rw [hh,pack_back] at he; exact he.symm

def allele (T: Tile (Biglot I) (t+1))(x:chain I (t+1))(p:Shift (Keys t)):= T (packSlot x p)
lemma ship_back (T:Tile (Biglot I) (t+1))(h: Up T)(x:chain (Biglot I) (t+1)): allele T (arcType x) (arcSlot x)=T x:= by rw [allele,← h (x 0).1, pack_back]
lemma allele_width (T: Tile (Biglot I) (t+1))(h:Bail (fame _) σ T A)(hs:0≤σ)(x:chain I (t+1)): Width (σ/((t:ℝ)+1)) A (allele T x):= by
   let w:=(t:ℝ)+1; let s:=σ/w;have hw:0<w:=by unfold w; positivity
   let k(p:Shift (Keys t)):pack (0:Fin (t+1)) (show Biglot I from (0,x 0)):=
        ⟨packSlot x p,rfl⟩
   have hk : Injective k:= fun p q hu=> (pack_shift x p).symm.trans ((congr_arg (fun z=>arcSlot z.val) hu).trans (pack_shift x q))
   refine ⟨fun p=>by positivity,from_evil h.1 (fun _=> by positivity) ?_⟩
   refine le_trans ?_ (h.watch k hk); apply ENNReal.tsum_le_tsum; intro p; rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm]; unfold glitter shine; apply mul_le_mul_left
   refine ENNReal.ofReal_le_ofReal (Real.exp_monotone ?_);let a:=wide (fame _) (packSlot x p)
   have he := pack_extent (packSlot x p); rw [pack_shift] at he; change size p≤(t+1)*a at he
   have hh : (size p:ℝ) ≤ w*a:= by unfold w; exact_mod_cast he
   exact (mul_le_mul_of_nonneg_left hh (show 0≤s by unfold s; positivity)).trans_eq (by change s*(w* a)=σ*a;unfold s;field_simp)
lemma width_count {p:Type}[Fintype p]{f:Shift p → ℝ}(h:Width σ A f):(∑' x,shine σ (size x)*‖f x‖ₑ)≤ ENNReal.ofReal A:= by
    unfold shine;simp_rw [← ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le,←ENNReal.ofReal_tsum_of_nonneg h.1 h.2.1]; exact ENNReal.ofReal_le_ofReal h.2.2
lemma allele_bill (T: Tile (Biglot I) (t+1))[Fintype I](h: Up T)(hp:∀ x,Width σ A (allele T x))(hs:0≤σ)(hz:0≤A): Bail (fame _) (σ/2) T (Fintype.card (chain I (t+1))*A):= by
    refine ⟨by positivity,fun i p=>?_⟩
    let f (u: chain I (t+1) × Shift (Keys t)):= shine σ (size u.2)*‖allele T u.1 u.2‖ₑ
    have hF: (∑' u,f u)≤ENNReal.ofReal (Fintype.card (chain I (t+1))*A):= by unfold f;rw [ENNReal.tsum_prod',←dust_cost (chain I (t+1)) A]; exact ENNReal.tsum_le_tsum fun x=>width_count (hp x)
    refine le_trans ?_ ((ENNReal.tsum_comp_le_tsum_of_injective (pack_unique i p) f).trans hF);apply ENNReal.tsum_le_tsum; intro v
    unfold f; dsimp only; rw [ship_back T h v]; unfold glitter shine; apply mul_le_mul_left; refine ENNReal.ofReal_le_ofReal (Real.exp_monotone ?_); have he : (wide (fame _) v.val:ℝ)≤ 2*size (arcSlot v.val):= by exact_mod_cast pack_refine _
    nlinarith
end YM.FormalBulk08.Broc
