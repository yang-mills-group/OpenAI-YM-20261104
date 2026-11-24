import YangMills.WilsonProof.NativeSupport.YM.MS.Pearl.Flats
/-!
# Press stationarity through weights κ and s
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{m n h i:ℕ} {V W:Flats G} {F:Mob G}{x:ℂ}
abbrev Vibe (h:ℕ)(F H: Flats G): Prop:=∀ᶠ i in dotty, ∀ ℓ,Mell.Trail (F ℓ i) (H ℓ i) (vamp i h ℓ)
abbrev Stay (h:ℕ)(F: Flats G): Prop:= ∀ y t,Live (Parade F h y t)
lemma work (he:Rent V n)(hv:Vibe h V W): Rent W n:= fun ℓ => (R_prev0 (he ℓ) (hv.mono fun _ hi=> hi ℓ)).live
lemma cohabit (he: Rent V n)(hP: Vibe h V W) (m:ℕ)(s y:ℝ): speed (fun t=>plow (-(h:ℂ)) t (Press V m n (y+t))) (plow (-(h:ℂ)) s (Press W m n (y+s))) s:= by
   let f:= V.support ∪ W.support; simp_rw [ raypage (m:=m) (n:=n) f ( Finset.subset_union_left (s₁:=V.support) (s₂:=W.support)), raypage (m:=m) (n:=n) f ( Finset.subset_union_right (s₁:=V.support) (s₂:=W.support)), ←cert,map_sum]; exact speed_sum _ (fun i hi=> Blink (he i) (hv:=hP.mono fun u hu=> hu i) m s y)
-- interpret pole coeffs via speed=0, then Hone
variable (he: Rent V n)(hv: Vibe h V W)(ht: Stay h W) (hm:i<n)
include he hv ht hm
lemma perm (t y:ℝ): plow (-(h:ℂ)) t (Press V i n (y+t))=Press V i n y:= by
    funext m l; let x:= -(h:ℂ); let U (s:ℝ):=Press V i n (y+s); let P(s:ℝ):= plow x s (U s) m l
    have hu s: HasDerivAt P 0 s:= by
       obtain he' := cohabit he hv i s y m l; rw [ Pick.unique (press_pick (work he hv) h s y) (dry (ht y s) _ hm)] at he'; exact he'
    obtain hx:=is_const_of_deriv_eq_zero (fun s=> ( hu s).differentiableAt ) (fun s=> (hu s).deriv) t 0; simpa only [P,U,posing,add_zero] using hx
lemma assign_p : ∃ F:Mob G, Home F h∧ F= Tad F h ∧ ∀ y, F=Press V i n y:= by obtain ⟨N,H⟩:=press_ready (n:=n) (F:=V) i; exact post_time _ H (pressB he i) (perm he hv ht hm)
lemma assign_home : Home (Press V i n 0) h∧∀ y,Press V i n 0=Press V i n y:= by obtain ⟨F,hV,hF,H⟩:= assign_p he hv ht hm; exact ⟨ H 0 ▸ hV, fun y=> (H 0).symm.trans (H y)⟩
omit he hv ht hm
-- pure subtraction artifact

def Mint (n:ℕ)(V:Flats G): Coat G:= ∑ i∈ Finset.range n, Ice (n-i) (Press V i n 0)
lemma minted (n:ℕ)(V:Flats G): Cool (Mint n V):= by apply (cone G).sum_mem (t:=Finset.range n) (f:=fun i=>Ice (n-i) (Press V i n 0)); intro i hi; exact iceC _ _ (by simp at hi; omega)
lemma Home_fin {f:I→ Mob G}(s:Finset I)(h:∀ i∈s,Home (f i) n): Home (∑ i∈s,f i) n:= by intro t; rw [← cert,map_sum]; exact Finset.sum_congr rfl fun i hi=> h _ hi _
include he
lemma MintC (Q:LeanC G)(h:Need Q)(hs:∀ i, To (V i) Q) (x:ℂ): Mint n V x∈Q:= by rw [Mint,Finset.sum_apply]; exact Q.sum_mem fun i hi=> Q.smul_mem (x⁻¹^(n-i)) (viewP V i n Q h he hs 0)
lemma MintR (Q:LeanR G)(h:Will Q)(hs:∀ i, realAlong (V i) Q)(x:ℝ): Mint n V x∈Q:= by rw [Mint,Finset.sum_apply]; refine Q.sum_mem fun i hi=>?_; unfold Ice; rw [← Complex.ofReal_inv,← Complex.ofReal_pow,reality]; exact Q.smul_mem _ ( viewR V i n Q h he hs 0)
lemma Mint_price (i:ℂ): kPrice (Mint n V i):= by rw [Mint,Finset.sum_apply]; exact fall_sum _ (f:=fun i' (_:Unit)=>Ice (n-i') (Press V i' n 0) i) (fun j _=> cost_k (pressB he j 0) _) (fun _=>zero_le_one) -- binder Unit check
lemma Mint_cap : altitude n ( Mint n V):= by unfold Mint altitude; rw [paidSum]; exact Live.fin _ (fun i hi=> lamp (pressB he i 0) ( Nat.sub_le n i))
include hm
lemma Mint_pick : Pick i (paid n (Mint n V)) (Press V i n 0):= by
    unfold Mint; rw [ paidSum]; obtain hK:= Pick.fin (Finset.range n) (fun j _=> icePick (j:=i) (pressB he j 0) (Nat.sub_le n j)); convert hK using 1; rw [Finset.sum_eq_single i]; rw [if_pos (by omega:i=n-(n-i))]; intro j hj he; rw [if_neg (by simp at hj; omega: i ≠ n-(n-j))]; intro hp; exact (hp (Finset.mem_range.mpr hm)).elim
include hv ht
omit hm in lemma minted_home (z:ℂ): Home (Mint n V z) h:= by rw [Mint,Finset.sum_apply]; exact Home_fin _ (fun i hi=> (assign_home he hv ht ( Finset.mem_range.mp hi)).1.smul _)
lemma brig_zero (s y:ℝ): Pick i (paid n (Parade (V-.single 0 (Mint n V)) h y s)) 0:= by
    rw [page_sub,pureP _ (minted_home he hv ht)]; rw [show paid n (Parade V h y s - Mint n V)=paid n _-paid n _ from funext fun i=> smul_sub (i^n) (Parade V h y s i) (Mint n V i)];
    obtain Y:= (press_pick (m:=i) he h s y).add ((Mint_pick he hm).static (-1)); rw [neg_one_smul, neg_one_smul, perm he hv ht hm,← (assign_home he hv ht hm).2 y, add_neg_cancel] at Y; simpa only [sub_eq_add_neg] using Y
omit hm in lemma correspondent : Stay h (V-Finsupp.single 0 ( Mint n V)):= by intro y t; apply reveal (n:=n) _ (fun i hi=> brig_zero he hv ht hi t y); rw [page_sub,pureP _ (minted_home he hv ht)]; apply altitude.sub ?_ (Mint_cap he); exact (press_pick he h t y (m:=0)).live
end YM.MS.Pearl
