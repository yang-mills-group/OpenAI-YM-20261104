import YM.FormalBulk08.Borough.Stats
import YM.Price.Waits

/-! An auxiliary formal family is not an existential YM history.
Levels uses J→∞. For transfer of Lemma(kbulk) to the independent
constant-L,J prescription we embed arbitrary long finite windows. The price
polynomial will **NOT** change with this embedding. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Copula
open Filter Function Finset Lattice Laurent Bloch Precision RG
open Supply Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open scoped BigOperators Topology Classical Matrix
variable {X:Type} {G:Gauge} {K:KernelChoices}{W: Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{S:Sheet G}
open Borough
lemma fund_first (h:G.Simple) (S:Sheet G): ∃ M:ℕ,∀ L:Side, M≤L.val → Odd L.val → ∃ P:Rolls S,P.L S.first=L:= by
   choose A P using fun i=> Rolls.eventually_large S h i
   let T (i:ℕ):=(range (i+1)).sup A; have hu : Monotone T:=fun a b ha=> sup_mono (range_mono (by omega)); have hx i:A i ≤ T i:= le_sup (mem_range.mpr (by omega))
   refine ⟨T S.first,fun L hL hl =>?_⟩
   let R(i:ℕ):Side:= if i ≤ S.first then L else ⟨2*(L.val+T i)+1,by omega⟩
   refine ⟨⟨R,fun i=>?_,fun i j h=>?_⟩,?_⟩
   · by_cases hi:i≤S.first
     · simp only [R, if_pos hi]; exact P _ _ (((hx i).trans (hu hi)).trans hL) hl
     simp only [R, if_neg hi]; exact P _ _ ((hx i).trans (by simp;omega)) ⟨_,rfl⟩
   · change (R i).val≤(R j).val; by_cases hx:j≤S.first
     · simp only [R, hx,h.trans hx,↓reduceIte,le_refl]
     simp only [R, if_neg hx]; by_cases he:i≤S.first
     · simp only [if_pos he]; dsimp;omega
     simp only [if_neg he]; dsimp;have := hu h;omega
   change R S.first = L; simp [R]

def dummy : Stage:= ⟨⟨1,1/32,1,by norm_num,by norm_num,by norm_num,by norm_num⟩,6,2,1,12,1,1,1,le_rfl,le_rfl,by norm_num,by norm_num,by norm_num,by norm_num,le_rfl,zero_le_one⟩
def tilled (G:Gauge)(K:KernelChoices)(f:ℕ→ℕ)(j:ℕ)(hp:∀ p:Patch,p.Branches K G)(h:4≤j) : Sheet G:= ⟨K,hp,fun _=>dummy,j,h,monotone_const,monotone_const,monotone_const,f⟩
-- Clock age flat on the requested portion. Auxiliary price after the
-- window paid by width-order stage delays. This lets us import
-- W.Loans even for the two-sided integer window.
def sealedTime (A:Schedule)(i:ℕ): Time ℕ:= ⟨fun x=>1+max 0 (A.scale x-A.scale i),fun _=> le_add_of_nonneg_right (le_max_left ..)⟩
lemma under_time (A:Schedule){m n:ℕ}(h:m≤n): (sealedTime A n).day m=1:=by
   dsimp [sealedTime]; rw [max_eq_left,add_zero]; have := sowing_plus A h; unfold sowing at this; linarith
lemma age_build (A:Schedule)(i:ℕ){m n:ℕ}(h:m ≤ n): (sealedTime A i).day n≤ (sealedTime A i).day m + sowing A m n:=by
   dsimp [sealedTime]; rw [add_assoc]; apply add_le_add_right; apply max_le; exact add_nonneg (le_max_left ..) (sowing_plus A h); refine le_trans (b:=(A.scale m-A.scale i)+sowing A m n) ?_ (add_le_add_left (le_max_right ..) _);unfold sowing; linarith

variable {P:Rolls S}{T:Protection P}{U:Empire G K X}
-- buy under flat age via credits
lemma delay_install (hG:G.Simple) (P:Rolls S)(E:ℕ→ℝ)(he:∀ i,0≤ E i)(N:ℕ): ∃ A:Levels G,A.clock.factor=P.L ∧ A.clock.kernel=S.kernel ∧ (∀ i,i≤N→A.clock.J i=S.first) ∧ ∀ i,E (A.clock.J (i+1))≤E S.first+(sealedTime A.S N).day i := by
   obtain ⟨T,-⟩:= Protection.exists_margin P (fun _=>1) (fun _=>zero_lt_one)
   let c:=Real.log ((P.L S.first).val:ℝ); have hc:0 ≤ c:= Real.log_nonneg (by exact_mod_cast (P.L S.first).property)
   let V: Delays T:= ⟨fun _=>0,fun j _=> (N:ℝ)*c+E j+1,fun _=>0,fun _=>0⟩; obtain ⟨B,-⟩:= Bar.exists_above V 1
   let X: Wait B := ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩; obtain ⟨A,h⟩:=Wait.ready X hG
   have hp' (i:ℕ)(hx:A.clock.J (i+1)≠S.first):(N:ℝ)*c+E (A.clock.J (i+1))+1≤A.S.scale i:= h.paysHigher _ (lt_of_le_of_ne (by rw [← h.firstZero]; exact A.fits.mono (Nat.zero_le _)) (Ne.symm hx))
   have ht(i:ℕ)(hv:i≤N): A.clock.J i=S.first ∧ A.S.scale i=(i:ℝ)*c:=by
      induction i with
      | zero=> exact ⟨h.firstZero,by simp⟩
      | succ i ih=>
        obtain ⟨-,hx⟩:= ih (by omega)
        by_cases hz:A.clock.J (i+1)=S.first
        · refine ⟨hz,?_⟩; rw [Schedule.scale_succ,hx,←A.fits.sameFactor,h.lengths,hz]; push_cast;ring
        have hh:=hp' _ hz; rw [hx] at hh; have : (i:ℝ)*c≤N*c:= mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_of_succ_le hv).le) hc; linarith [he (A.clock.J (i+1))]
   refine ⟨A,h.lengths,h.kernel,fun i hi=>(ht i hi).1,fun i=>?_⟩
   by_cases hh:A.clock.J (i+1)=S.first
   · rw [hh]; exact le_add_of_nonneg_right ((sealedTime _ _).good _)
   have hv:= hp' _ hh; dsimp [sealedTime]; have hz:0 ≤ E S.first:= he _; have hq:= (ht N le_rfl).2; have h': A.S.scale i-A.S.scale N ≤ max (0:ℝ) (A.S.scale i-A.S.scale N):= le_max_right ..;linarith
end YM.FormalBulk08.Copula
