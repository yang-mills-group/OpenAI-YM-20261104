import YM.MS.Wind.Path
/-!
# Consistency of heat derivation in a Scale tape

Real log-argument parameter integral with lengths in native. Symbols in ℂ. Ward PDE not just
 identity for configurations; follows the actual solutions via Pieces mapping. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge}{p:Team}{φ: Actor G}{F H: Dec G}{X Y:T (Law G)}{u:ℤ}

abbrev Ω (G:Gauge)(t:ℝ): GridR (Law G) := rack (Cpu G t) (Mood G t) (Z G) μzone

def payR (F:Dec G)(x:ℝ)(t:ℝ): T (Law G):= fun i=> F i x t
lemma centered (h:PC G p F)(x t:ℝ): payR F x t 0=0:= by simp [payR,h.free]
-- circumscription
local notation "I_f"=> (2:ℂ)⁻¹
local notation "Kx"=> F -- maybe shadow hidden R.A.
lemma quarterback (c:ℝ)(n d:ℕ)(i:Dec G)(j: Dec G) (x t:ℝ): (path c n d i j x t)= (c:ℂ) • ∑ k∈ Domain.paths n d, (Ω G t).X (i (n-k) x t) (j k x t):=by rw [path, Pi.smul_apply, Pi.smul_apply,Finset.sum_apply,Finset.sum_apply]; rfl
lemma raising (h:PC G p F) (n:ℕ)(x t:ℝ)(h0:0<n) : (Ω G t).grow (payR F x t) n=Wiref G (F n x) t+(path (1/2) n 1 F F x t) := by
   let Y:=(Ω G t).X; let X:=payR F x t; let V:= Y; change _+ I_f • (∑ i∈antidiagonal n,Y (X i.1) (X i.2))=_; rw [canon_corner (fun i j=> Y (X i) (X j)) _ h0, show X 0=0 from centered h x t,map_zero,map_zero,LinearMap.zero_apply,zero_add,zero_add,quarterback]; push_cast; rw [one_div]; rfl
lemma raising_M (h:PC G p F)(n:ℕ)(x t:ℝ)(H:Dec G): (Ω G t).lives (payR F x t) (payR H x t) n=Wiref G (H n x) t+(path 1 n 0 F H x t):= by
   let X:=(Ω G t).X; let V:=payR F x t; let Y:= payR H x t; change _ +(∑ i∈antidiagonal n,X (V i.1) (Y i.2))=_; rw [canon_sub (fun i j=>X (V i) (Y j)) n, show V 0=0 from centered h x t,map_zero,LinearMap.zero_apply, zero_add,quarterback,Complex.ofReal_one,one_smul]; rfl
lemma prior (h:PC G p F)(x t:ℝ)(n:ℕ): Zip (F n x) ((Ω G t).grow (payR F x t) n) t:= by
   rcases n with _|n; swap; · rw [raising h (n+1) x t (by omega)]; exact (h.recu _ (by omega) x).2 t
   unfold GridR.grow; simp [payR,h.free,paired,promised,Zip]; exact hasDerivAt_const ..
lemma priorM (h:PC G p F)(hP:PM φ F H u)(x t:ℝ)(n:ℕ): Zip (H n x) ((Ω G t).lives (payR F x t) (payR H x t) n) t:= by rw [raising_M h]; exact (hP.recu n x).2 t

section calculus
variable (x t:ℝ) (C:ℂ) {b:Bool}
local notation "T0"=> payR F x -- notation hygiene from F implicit nonshadow
local notation "V0"=> payR H x
local notation "K"=>Ω G
variable (hf:∀ i, TouchF (F i x)) (he:∀ i, TouchF (H i x))
 (hk:∀ i, Zip (F i x) (X i) t)(hp:∀ i, Zip (H i x) (Y i) t)
-- derivative linear assumptions not a posteriori. Use It.
include he hp
lemma Jpart (hP:∀ i,Pass (Mood G t) (Y i) μzone) (i:ℕ): Zip (fun s=>promote ((K s).J) (V0 s) i) (promote ((K t).J) Y i + promote ((K t).L) (V0 t) i ) t:= by
    obtain hx:= orbit_zip μzone cour0 (mood_f _) (he i) (period0 μzone cour0 (then_f G) (he i)) (hP i) (f_der G t) (hp i)
    intro w; convert! (ZQ (Z G) (hp i) w).add (hx w) using 1; simp only [Pi.add_apply,promised,Ω,payR,rack,LinearMap.add_apply,Pi.add_apply]; abel
include hk
omit he in
lemma Cpart (i:ℕ): Zip (fun s=> pairW (K s).C (T0 s) (V0 s) i) (pairW (K t).D (T0 t) (V0 t) i + pairW (K t).C X (V0 t) i + pairW (K t).C (T0 t) Y i) t:= by
   simp_rw [paired, ← Finset.sum_add_distrib]; refine Zip.sum _ (fun j _=> tree_zip (Xrev G) (Yrev G t) (f_der G t) (hk j.1) (hp j.2))
omit hp hk he
include hf
lemma liveTouch (J:ℝ→Flux (BH G) QP ℂ)(hJ:flex J)(hr:∀ i,Reverse (J i) parity)(hH : ∀ i,TouchF (H i x))(i:ℕ): TouchF (fun t=>pairW (boulevard parity (J t)) (T0 t) (V0 t) i) := TouchF.sum (antidiagonal i) (fun f _=> tree_touch hr hJ (hf f.1) (hH _)) -- syntax
omit hk
lemma growT (i:ℕ): TouchF (fun t=> (K t).grow (T0 t) i):= TouchF.add (lapid_touch (hf i) (main_f _)) ((liveTouch x hf (Cpu G) (main_f G) (Vrev G) hf i).scale (2:ℂ)⁻¹) -- check
include he
lemma livesT (i:ℕ): TouchF (fun t=>(K t).lives (T0 t) (V0 t) i):= TouchF.add (lapid_touch (he i) (main_f G)) (liveTouch x hf (Cpu G) (main_f G) (Vrev G) he i)
end calculus
end YM.MS.Wind
