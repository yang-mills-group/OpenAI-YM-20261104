import YangMills.WilsonProof.NativeSupport.YM.MS.Book.Mask
import YangMills.WilsonProof.NativeSupport.YM.MS.WardSquares
/-!
# Bodywise ∆ and Q at finite perturbation order

Graded extraction along row of vertices without power division.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book
open Function Filter Set Finset Plane Koszul Cylinder Lab
variable {A I R:Type*}[CommRing R] {p:Sector A} {F H: Raw A R} {h g:ℤ}

def rankLevel (h:ℤ)(F:Raw A R)(n:ℕ) := mask (n+h) F
local infixl:70 " ⋄ "=> product p
lemma mask_spin (b:Bool)(n:ℕ)(F:Raw A R): Koszul.sign p b (rankLevel h F n)= rankLevel h (Koszul.sign p b F) n := sign b -- autoImplicit false
lemma mask_conn (f:Raw A R)(i:A)(n:ℕ): D i (rankLevel h f n)=rankLevel (h-1) (D i f) n:= by rw [rankLevel,conn,rankLevel]; congr 2; omega
lemma pairLevel (n:ℕ) (hF:From F h)(hH:From H g): (∑ i∈ antidiagonal n,(rankLevel h F i.1) ⋄ (rankLevel g H i.2))= rankLevel (h+g) (F ⋄ H) n:= by
    have hr : rank (n+(h+g)) (∑ i∈ antidiagonal n, (rankLevel h F i.1) ⋄ (rankLevel g H i.2)):= by
        apply Rails.sum; intro i hi; obtain he:=mem_antidiagonal.mp hi; rw [show (n:ℤ)+(h+g)=(i.1+h)+(i.2+g) by omega]; exact (rankMod F (i.1+h)).product (rankMod H (i.2+g))
    ext w; by_cases hx:(w.length:ℤ)=n+(h+g); swap
    · unfold rankLevel; rw [strange _ hx]; exact hr w (by rw [mod_int]; exact hx)
    rw [show rankLevel _ _ n w=_ from enough w hx, Finset.sum_apply];
    let Q (U W:Raw A R): Shared A R:= fun l r=> U l * W r
    simp_rw [show ∀ U W:Raw A R,(U ⋄ W) w=allocate p w (Q U W) from fun _ _=> scattered .., ← map_sum];
    apply scatter_congr; intro l r he; simp only [Finset.sum_apply,Q]; obtain hh:=split_length he
    by_cases ha:h≤l.length; swap; · rw [hF l (by omega),zero_mul]; refine Finset.sum_eq_zero (fun i _=> by unfold rankLevel; rw [From.tag hF (i.1+h) l (by omega),zero_mul]) -- unfold
    by_cases hb:g≤r.length; swap; · rw [hH r (by omega),mul_zero]; refine Finset.sum_eq_zero (fun i _=> by unfold rankLevel; rw [From.tag hH (i.2+g) r (by omega),mul_zero])
    let I : ℕ:=(l.length-h).toNat; let J:ℕ := (r.length-g).toNat
    unfold rankLevel; rw [Finset.sum_eq_single (I,J), enough _ (show (l.length:ℤ)=(I:ℤ)+h by unfold I; omega), enough _ (show (r.length:ℤ)=(J:ℤ)+g by unfold J; omega)]
    · rintro ⟨x,y⟩ _hu hu; by_cases he:(l.length:ℤ)=x+h
      · rw [strange _ (show (r.length:ℤ) ≠ y+g from fun h=> hu (Prod.ext (by unfold I; dsimp only; omega) (by unfold J; dsimp only; omega))), mul_zero]
      rw [strange _ he,zero_mul]
    exact fun ht=> (ht (mem_antidiagonal.mpr (by dsimp only [I,J]; omega))).elim
lemma link_level (B: Bonded p I)[Fintype I] (n:ℕ)(hF:From F h)(hH:From H g):
   ∑ k∈antidiagonal n, link B.BV true p (rankLevel h F k.1) (rankLevel g H k.2)= rankLevel (h+g-2) (link B.BV true p F H) n:= by
   simp_rw [Bonded.BV,loop,link_sum,link_scale]; rw [Finset.sum_comm]; simp only [rankLevel,map_sum,map_smul]; refine Finset.sum_congr rfl (fun i _=> ?_)
   let a:=B.dual i; let b:=B.plain i; let f:= Koszul.sign p (p b) (D a F); let f' := D b (Koszul.sign p (p a) F)
   rw [← Finset.smul_sum]; congr 1; simp_rw [link_pair (B.dual i) _ (B.op i),conn, sign,conn,Finset.sum_add_distrib,map_add]; -- unfold
   have hz (s u:ℤ): s+u-1=s+(u-1):= by omega
   simp_rw [hz]; rw [show h+g-2=(h-1)+(g-1) by omega];
   congr 1 <;> first | exact pairLevel n ((hF.tip a).signs _) (hH.tip b) | exact pairLevel n ((hF.signs (p:=p) _).tip b) (hH.tip a)
lemma lap_level (B: Bonded p I)[Fintype I] (n:ℕ): B.BV (rankLevel h F n)=rankLevel (h-2) (B.BV F) n:= by
    simp_rw [Bonded.BV,loop,LinearMap.sum_apply,LinearMap.smul_apply,diffPair_apply,mask_conn]; unfold rankLevel; simp_rw [map_sum,map_smul]; rw [show (h-1-1)=h-2 by omega]
lemma roofLap (B:Bonded p I)[Fintype I](hF:Limit F h): Limit (B.BV F) (h-2):= by
    rw [show h-2=h-1-1 by omega]; simp only [Bonded.BV,loop,LinearMap.sum_apply,LinearMap.smul_apply]; exact Limit.sum _ (fun i _=> ((hF.tip _).tip _).smul _)
lemma roofLink (B:Bonded p I)[Fintype I](hF:Limit F h)(hH:Limit H g): Limit (link B.BV true p F H) (h+g-2):= by
    rw [show h+g-2=(h-1)+(g-1) by omega]; simp_rw [Bonded.BV,loop,link_sum,link_scale,link_pair _ _ (B.op _)]; exact Limit.sum _ (fun i _=> Limit.smul _ ((((hF.tip _).signs _).pair (hH.tip _)).add (((hF.signs _).tip _).pair (hH.tip _))))
end YM.MS.Book
