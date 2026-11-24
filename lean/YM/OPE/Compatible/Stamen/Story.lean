import YM.OPE.Compatible.Stamen.Scroll
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
lemma leadV (f g:ℝ→ℝ)(n:ℕ)(h:ContDiff ℝ ⊤ f)(hp:ContDiff ℝ ⊤ g): leading n (f*g)=∑ i∈range (n+1),leading i f*leading (n-i) g:=by
      unfold leading; rw [iteratedDeriv_mul (h.of_le le_top|>.contDiffAt) (hp.of_le le_top|>.contDiffAt),Finset.smul_sum]; refine sum_congr rfl ?_; intro i hi; have ht:= (show i≤n from Nat.le_of_lt_succ (mem_range.mp hi)); have he : (n.choose i:ℝ)*i.factorial*(n-i).factorial=n.factorial:=by exact_mod_cast Nat.choose_mul_factorial_mul_factorial ht
      simp only [smul_eq_mul]; field_simp; -- rw
      ring_nf at he ⊢
      rw [he]; ring
lemma signalV (f g:ℝ→ℝ)(hf:f 0=0)(hp:∀ i:ℕ,i < k→leading i g=0)(h:ContDiff ℝ ⊤ f)(hg:ContDiff ℝ ⊤ g)(j:ℕ): leading (k+1+j) (f*g)=∑ i∈range (j+1), leading (i+1) f*leading ((k+1+j)-(i+1)) g:=by
     rw [leadV _ _ _ h hg, sum_range_succ']; have hz : leading 0 f=0:=by simp [leading,hf]
     rw [hz,zero_mul,add_zero]; symm; refine sum_subset (range_mono (by omega)) (fun i h hi=>?_ )
     rw [hp _ (by have hp:= mem_range.mp h; have hl: i≥ j+1:=Nat.not_lt.mp (fun z=>hi (mem_range.mpr z)); omega),mul_zero]
-- Packed tokens.OUT.m and hor.
abbrev pageFlow (u:Page (Shade H) k)(v:fieldX (Shade H))(t:ℝ):ℝ:= wordX (fun _=> board (lotU (t • v))) u
lemma pageQ (u:Page (Shade H) k)(v:fieldX (Shade H))(k':ℕ): leading k' (pageFlow u v)=wholeX (coff (ships u) k') (fun _=>v):=by rw [← coinShots, show pageFlow u v=(fun t:ℝ=>verseX _ _) from funext fun t=>issue u _]
lemma boundPack (u:Page (Shade H) k)(v:fieldX (Shade H)) (k':ℕ)(h:k'<k): leading k' (pageFlow u v)=0:=(pageQ u v k').trans (sifts_nil u v h)
lemma smoothP (u:Page (Shade H) k)(v:fieldX (Shade H)): ContDiff ℝ ⊤ (pageFlow u v):=by
      rw [show pageFlow u v=(fun t:ℝ=>verseX (ships u) (lotU (t • v))) from funext fun t=>issue u _]; exact cash_smooth ..
abbrev windX (v:fieldX (Shade H))(a: Root (Shade H)):Token:=⟨mores v 1 a,mores v 2 a,mores v 3 a⟩
abbrev chiff (u:Page (Shade H) k)(v:fieldX (Shade H)):Token:=⟨leading k (pageFlow u v),leading (k+1) (pageFlow u v), leading (k+2) (pageFlow u v)⟩
lemma stage_P (a:Page (Shade H) (k+1))(v:fieldX (Shade H)): chiff a v=windX v (a 0)*chiff (mort a) v:=by
     let u:=mort a; let f:=sheetM (a 0) v; let g:= pageFlow u v; have he: pageFlow a v=f*g:=funext fun i=>Fin.prod_univ_succ _; have hp(j:ℕ): leading (k+1+j) (pageFlow a v)=∑ i∈range (j+1), leading (i+1) f*leading (k+j-i) g:=by
           rw [he,signalV f g (chargeP ..) (fun i=> boundPack u v i) (smoothZ ..) (smoothP ..)]; refine sum_congr rfl fun i _=>by rw[show k+1+j-(i+1)= k+j-i by omega]
     apply JetS.eta
     · have hz:=hp 0; rw [show 0+1=1 from rfl,sum_range_one] at hz; exact hz
     · have hz:=hp 1; simp only [sum_range_succ,sum_range_zero,zero_add,Nat.sub_zero,Nat.add_sub_cancel] at hz; exact hz
     have hz:=hp 2; simp only [sum_range_succ,sum_range_zero,zero_add,Nat.sub_zero,Nat.add_sub_cancel] at hz; exact hz
lemma amassed (u:Page (Shade H) k)(v:fieldX (Shade H)): chiff u v= ∏ i,windX v (u i):=by
     induction k with
     | zero=> rw[Fin.prod_univ_zero]; have ht:pageFlow u v=fun _=>1:=funext fun _=> Fin.prod_univ_zero ..; unfold chiff; rw [ht]; simp [leading,iteratedDeriv_const]; rfl
     | succ k ih=> rw[Fin.prod_univ_succ, stage_P u v, ih]; rfl
end YM.OPE.Silt.Phere
