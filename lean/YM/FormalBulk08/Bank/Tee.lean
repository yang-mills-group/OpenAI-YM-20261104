import YM.FormalBulk08.Bank.Eerie

/-! Lift off. Authority is torus Ward. Strips here existential only per
step/horizon, NO higher jet estimates yet. Normalization per primitive ratio
pending. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (T : Lodge P.patch) (W : Pot G) (ρ : ChartRatio G) (h : P.patch.Branches K G)

def sapkin (G : Gauge) (k : ℝ) (V : Train j) (r : ℕ) : Tile (edgeL G) r:= if h:r=2 then lengthen h.symm (setkin G (pink k V)) else 0
def waken : Pot G:=fun e r=> if e=0 then sapkin G K.penalty P.land r else if r=0 then 0 else coastRun P T W ρ h e r
lemma landry : waken P T W ρ h 0 2=setkin G (pink K.penalty P.land):=by rw [waken,if_pos rfl,sapkin,dif_pos rfl]; rfl

-- reusable
lemma head_bill (V : Train j) (k : ℝ) (hk : 0 < k) (hj:4≤j) (r):Up (sapkin G k V r) ∧ ∃ s C:ℝ, 0<s ∧ Bail (fame _) s (sapkin G k V r) C := by
   by_cases hx:r=2
   · subst r; rw [sapkin,dif_pos rfl]; obtain ⟨s,C,h,hc,hv,-⟩:= colors G k hk hj; obtain ⟨B,hB,hp⟩:= setkin_pay G h.le; exact ⟨up_smooth (up_couple _),s,_,h,hp (pink k V) _ hc.le (hv V).1⟩
   rw [sapkin,dif_neg hx];exact ⟨up_zero _,1,0,by norm_num,bail_void ..⟩
lemma head_forms (V : Train j) (k : ℝ) (hk : 0<k) (hj : 4≤j) (r) (i:Fin r) (n) : marble r (crunch (kernelP G k V n))=cum i n (sapkin G k V r):= by
   by_cases he:r=2
   · subst r; rw [sapkin,dif_pos rfl]; obtain ⟨s,C,h,hc,hp,-⟩:= colors G k hk hj;exact (setkin_folds G _ h.le hc.le (hp V).1 n i).symm
   rw [sapkin,dif_neg he,cum_zero,marble_eq_zero_iff,MvPolynomial.homogeneousComponent_of_mem (kinetic_grade _),if_neg he]
-- arbitrary finite simmer
variable (hp : Story W (pink K.penalty P.wing)) (ht : 4 ≤ t) (hr : LocalRatio ρ) (k : ∀ n, (primary P.patch K n).Choices)
def burn (n : Side) := landed P ρ h T n (k n) (stone W _)
include hp ht hr
lemma funded (n : Side): coeff 0 (burn P T W ρ h k n)=crunch (kernelP G K.penalty P.land n) := by
   refine landed_cost P ρ h T _ _ _ ?_ hr ht
   obtain ⟨s,C,h,hc,hv,-⟩:= colors G K.penalty K.penalty_pos P.legal;exact stoned_main h.le hc.le (hv _).1 hp.toVivid hp.ink _
lemma componentwise (e r : ℕ) (i: Fin r) :
    let f:=burn P T W ρ h k
    ∃ η:ℝ, 0<η ∧ Kith η (waken P T W ρ h e r) (fun n=> rancho (f n) e r) := by
   intro f; unfold waken
   cases e with
   | zero=>
      obtain ⟨hu,s,C,hs,H⟩:=head_bill (G:=G) P.land K.penalty K.penalty_pos ht r
      simp only [↓reduceIte];unfold f rancho; simp_rw [funded P T W ρ h hp ht hr k, head_forms _ K.penalty K.penalty_pos ht r i]; exact ⟨s,hs,stable hs.le hu H i⟩
   | succ e=>
      simp_rw [if_neg (show ¬ e+1=0 by omega),if_neg (show ¬ r=0 by have := i.isLt;omega)];unfold f burn; obtain ⟨s,C,hs,hC,H⟩:= aone P (K:=K) G ht
      have he n := read_tor P T W ρ h hr hp hs hC H n (k n) ht e r
      simp_rw [he]; exact bank_skin P T W ρ h hp hr k ht (e+1) r i
lemma emperor (n:Side) : Civic (burn P T W ρ h k n) := by
   refine landed_ward P ρ h T _ _ _ ?_ hr ht (hp.civic _)
   obtain ⟨s,C,h,hc,hv,-⟩:= colors G K.penalty K.penalty_pos P.legal;exact stoned_main h.le hc.le (hv _).1 hp.toVivid hp.ink _
lemma flameproof (n j r) (e : j+2 < r) : rancho (burn P T W ρ h k n) j r=0 := by
   obtain ⟨s,C,hs,hC,H⟩:=aone P (K:=K) G ht
   cases j with
   | zero=> rw [rancho,funded P T W ρ h hp ht hr k,marble_eq_zero_iff,MvPolynomial.homogeneousComponent_of_mem (kinetic_grade _),if_neg (by omega)]
   | succ j=> unfold burn; rw [read_tor P T W ρ h hr hp hs hC H n (k n) ht]; by_contra hx; obtain ⟨h₀,h₁,-⟩:=sailed_fin P T W ρ h hp.toVivid hr hs hC H n (k n) _ _ hx;omega
-- no `k` since chosen to witness Ward
lemma creed : Story (waken P T W ρ h) (pink K.penalty P.land) := by
   let k n:=Classical.choice (chooseable _ _ (primary P.patch K n)); let R:=burn P T W ρ h k
   have hg:=componentwise P T W ρ h hp ht hr k;have hC n:= emperor P T W ρ h hp ht hr k n
   let Z:= waken P T W ρ h
   have hv : Vivid Z := by
      have hx (e): Z e 0=0:= by simp [Z,waken,sapkin]
      refine ⟨fun e r=>?_,fun e r=>?_,fun j r he=>?_⟩
      · rcases r with (_|r)
        · rw [hx]; exact up_zero _
        obtain ⟨η,hη,H⟩:= hg e _ (0:Fin (r+1)); exact light_up H.1 (.of_forall fun n=>civic_up n _ (hC n) _ _)
      · rcases r with (_|r)
        · rw [hx];exact agate_zero _
        obtain ⟨η,hη,H⟩:= hg e _ (0:Fin (r+1)); exact light_agate H.1 (.of_forall fun n=>marble_agate _ (coeff e (R n)))
      by_cases h':r=0
      · exact False.elim (he (by rw [h',hx]))
      have hr':0<r:=by omega
      by_cases hj:j=0
      · subst j; unfold Z waken at he; rw [if_pos rfl,sapkin] at he; split at he; constructor;exact hr';constructor <;> omega;contradiction
      unfold Z waken at he; rw [if_neg hj,if_neg h'] at he; obtain ⟨-,h₁,h₂⟩:= sailed_val P T W ρ h hp.toVivid hr _ _ he; exact ⟨hr',h₁,h₂⟩
   refine { hv with
     ink:=landry P T W ρ h
     fare:=fun e r=>?_
     civic:=fun n=> civic_shore n R (stone Z n) Z (fun n=>n+2) (fun e r he=>hg e r (⟨0,he⟩ : Fin r)) (fun e r i=> hv.flower e r i _) (.of_forall hC) (fun e=>.of_forall fun n r l=>flameproof P T W ρ h hp ht hr k n e r l) }
   rcases r with (_|r)
   · have he: Z e 0=0:= by by_contra hh; exact Nat.lt_irrefl _ (hv.valence _ _ hh).1
     change ∃ η C,0<η ∧ Bail _ _ (Z e 0) C; rw [he]; exact ⟨1,0,by norm_num,bail_void ..⟩
   obtain ⟨s,hs,h,C,H⟩:=hg e _ (0:Fin (r+1)); exact ⟨s,C,hs,lit_width h C H⟩
end YM.FormalBulk08.Bank
