import YM.OPE.Compatible.Vines.Ranger
import YM.Pert.Lattice.Recovery
/-!
# Reading the degree-d radial quotient. Injectivity at leading weight, all ranks. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor ContinuousMultilinearMap WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{I T:Type*}{G:Gauge}
namespace Script
open Page
lemma clad (a:Shade G) (l:List Axis):∃ T:Ridge G l.length,∀ x j, ledge T (x,j)= if j=a then tasting l (translit x) else 0:=by
    let b:G.Color:=toLp 2 (Pi.single a.2 1); let p:= YM.Pert.Bare.spaceMon l.get b; let f: Ridge G l.length:=Pi.single a.1 p
    have he (x:E4): diagonal p x= tasting l (invertX x) • b:=by unfold p diagonal; rw [YM.Pert.Bare.mon_eq]; rw [← tastePower l x];rfl
    refine ⟨f,fun x j=>?_⟩; change diagonal (f j.1) _ j.2=_
    by_cases h:j.1=a.1
    · rw [show f _= p from h ▸ Pi.single_eq_same .. ,he]; by_cases hv:j.2=a.2
      · rw [if_pos (Prod.ext h hv)];simp only [hv, b,PiLp.smul_apply,Pi.single_eq_same]; change _*1=_; rw [mul_one]
      rw [if_neg (fun h=> hv (congr_arg Prod.snd h))]
      change _*b j.2=_; rw [show b j.2=0 from Pi.single_eq_of_ne hv _,mul_zero]
    rw [if_neg (fun y=> h (congr_arg Prod.fst y)),show f _=0 from Pi.single_eq_of_ne h _]; simp [diagonal]
lemma chimes {p: Script (Shade G) r}(hp:soot m p c)(h:p.abides) (ht:p.Bells n)(hh:n < m)
   (hx:∀ y:Fin r→ℕ,(∑ i,(y i+1))=n→∀ u:∀ i:Fin r,Taylor G (y i), wholeX p (fun i=>ledge (u i).val)=0):p.Bells (n+1):=by
     intro a l hl; by_cases he:l.length<n; exact ht a l he; have hL:l.length=n:=by omega
     let v i:= tasteE l i; let k(i:Fin r):=(v i).length; choose pX Hp using fun i=> clad (a i) (v i); let V i:= ledge (pX i)
     have hu(i:Bin r)(t:Ink (Shade G) r):wordX V (syn i t)= if t=a then tasting l (translit i) else 0:=by
         split
         next h => subst t; rw [topping]; unfold V wordX; refine prod_congr rfl fun j _=>?_ ; change ledge (pX _) ((stepOut i j),a j)=_; rw [Hp,if_pos rfl]; rfl
         next h => obtain ⟨j,hj⟩:=not_forall.mp (show ¬ ∀ j,t j=a j from fun g=>h (funext g)); exact prod_eq_zero (mem_univ j) (by change ledge (pX _) ((stepOut i j),t j)=_; rw [Hp,if_neg hj])
     have hr:(∑ j: Fin r,k j)=n:= (tram l).trans hL; let e:Ink (Shade G) r × Bin r≃Page (Shade G) r:= Equiv.trans (Equiv.prodComm ..) (blurb ..)
     have he: wholeX p V=well (sliceP p a) (tasting l):=by
         let f(i):= p i*wordX V i; have hS: Summable (f ∘ e):= e.summable_iff.mpr (wordSum hp (fun i:Fin r=> low_quiet (ledgeL (pX i))) (hr.trans_le hh.le))
         change (∑' i,f i)=_; rw [← e.tsum_eq f]; change (∑' i,(f ∘ e) i)=_; rw [hS.tsum_prod,tsum_eq_single a]
         · refine tsum_congr fun i=>?_; change p (syn i a)*wordX V (syn i a)=_; rw [hu,if_pos rfl];rfl
         intro b h; simp_rw [show ∀ i:Bin r,(f ∘ e) (b,i)=0 from fun i=> by change _*wordX V (syn i b)=0;rw [hu,if_neg h,mul_zero],tsum_zero]
     rw [← he]; change wholeX p (fun i=> ledge _)=_; rw [winds hp ht h pX hr hh]; by_cases H:∀ i, 1≤ k i
     · let y(i:Fin r):= k i -1; have hv(i):k i=y i+1:=by unfold y; exact (Nat.sub_add_cancel (H i)).symm
       have hg(i): ∃ u:Taylor G (y i), ledge (warp (pX i))=ledge u.val:= by
           suffices A : ∀ j:ℕ, j=y i+1→∀ T:Ridge G j,∃ u:Taylor G (y i),ledge (warp T)=ledge u.val from A _ (hv i) _
           rintro _ rfl T; exact ⟨fry T,rfl⟩
       choose u hh using hg; simp_rw [hh]; exact hx y (by simp_rw [← hv];exact hr) u
     obtain ⟨i,hj⟩:= not_forall.mp H; have hu:k i=0:=by omega
     have hv: ledge (warp (pX i))=0:=by
        suffices h: ∀ (d:ℕ), d=0→∀ T:Ridge G d, ledge (warp T)=0 from h _ hu _
        rintro _ rfl T; exact funext fun x=>by unfold ledge letterX; simp_rw [warp_base]; rfl
     unfold wholeX; simp_rw [show ∀ a:Page _ _,wordX (fun i=> ledge (warp (pX i))) a=0 from fun a=> prod_eq_zero (mem_univ i) (congr_fun hv (a i))]; simp
end Script
end YM.OPE.Flume
