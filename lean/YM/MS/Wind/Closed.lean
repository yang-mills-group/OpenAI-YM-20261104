import YM.MS.Wind.Realized
/-!
# Physical (perturbative) Ward coherence

Propagate exact identities to every t. Closure of Views at net0 for bulk; arbitrary marks in all
 independent momenta. Does not need HT estimates/Sl. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal Modeled
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge}{p:Team}{φ: Actor G}{F H: Dec G}{u:ℤ} {k:ℕ}{l:List (Lane4 G)}
variable (x:ℝ)
local notation "X"=> payR F x
local notation "Y"=> payR H x
local notation "ξ" => Ω G
local notation "pb"=> (2:ℂ)⁻¹

section
variable (H':G.Simple) (h:PC G p F)
include H' h
lemma realized (n:ℕ) : ∀ t:ℝ,∀ w:List (Lane4 G), net w=0→mat F x t n w=0:= by
    induction n using Nat.strong_induction_on with
    | _ n ih=>
       let U (t:ℝ) := mat F x t n; have ht:= total_slot x h (h.owes) n pb; have hv : Near true U:= by
           refine ⟨ht.1,ht.2,fun t w he=>?_⟩; let A := Ω G t; let M:= mat F x t
           obtain hl:= unit_field x h n w (he rfl) t
           have hm : A.lives (payR F x t) M n w= Wiref G U t w:= by
               unfold GridR.lives; rw [Pi.add_apply,paired,canon_sub (f:=fun i j=> A.X (payR F x t i) (M j)),centered h,map_zero,LinearMap.zero_apply,zero_add, Pi.add_apply, Finset.sum_apply, Finset.sum_eq_zero ?_, add_zero]; rfl
               intro j hj; let Q:=M j; have hx:Agrees Q 0:= fun l hl=> ih j (path_in hj).2 t l hl
               refine Eq.trans (agrees_tree (X t (n-j)) Q (Cpu G t) parity (fun _ _=>rfl) hx w (he rfl)) ?_; change (A.X _ 0) w=0; rw [map_zero]; rfl
           change HasDerivAt _ (A.lives (X t) M n w) t at hl; rw [hm] at hl; exact hl
       exact fun t w hw=> hv.gone (fun w hw=> r0 x h H' (hw rfl) n) w (fun _=>hw)
lemma solidmark (n:ℕ)(hm:PM φ F H u)(hp:Circle G φ false u)(ht:Weightless (Spectrum G) (style G p x) (φ x)): ∀ t:ℝ,res F H x t n=0:= by
    induction n using Nat.strong_induction_on with
    | _ n ih=>
       let U (t:ℝ) := res F H x t n; have hv : Near false U:= by
           obtain hk := total_slot x h (hm.owes) n 1; rw [show (fun t:ℝ=> (promote (ξ t).J (Y t)+ (1:ℂ) • pairW (ξ t).C (X t) (Y t)) n)= U from by funext i; rw [one_smul]; rfl] at hk
           refine ⟨hk.1,hk.2, fun t w _=> ?_⟩; let A:=Ω G t; let W:=res F H x t; let V:=A.lives (X t) W; let D:= mat F x t; let R:=payR F x t
           have HT : pairW A.X R W n=0:= by
               rw [paired,canon_sub (fun i j=> A.X (R i) (W j)), show R 0=0 from centered h x t,map_zero,LinearMap.zero_apply,zero_add]; exact Finset.sum_eq_zero (fun j hj=> by rw [show W j=0 from ih j (path_in hj).2 t,map_zero])
           have hK : pairW A.X D (payR H x t) n=0:= by
               rw [paired]; apply Finset.sum_eq_zero; intro i _; change boulevard parity _ _ _=0; rw [blvd]; let Q := payR H x t i.2; have ht : Agrees (D i.1) 0:= realized x H' h i.1 t; rw [tree_agrees _ _ (D i.1) _ _ ht]; exact (LinearMap.congr_fun (A.X.map_zero) Q).trans rfl
           obtain h0 := mark_field x h hm n t w
           change HasDerivAt (fun t=> U t w) ((V n + pairW A.X D (payR H x t) n) w) t at h0; rw [hK,add_zero, show V n=Wiref G U t from add_eq_left.mpr HT] at h0; exact h0 -- weird add_eq_??
       intro t; funext l; exact hv.gone (fun w hw=>congr_fun (initialS x h hm hp ht n) w) l (fun u=>Bool.noConfusion u)
end
end YM.MS.Wind
