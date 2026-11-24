import YM.SignedWilsonExpansion.F9.Looms
/-!
# Matrix solving at *actual K* on literal probe: price, boundary Σ, unit, rank tie
Avoid approximation by complex in this step; complete tag-lane with ℂ only outside.
-/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b Ñ_ N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
lemma Down.under {σ:Type*}[Fintype σ]{q:σ→ℕ}{M:Matrix σ σ ℝ}{x y:σ→ℝ}(h:Down q M B)
    (i:σ)(p:q i≤k)(hp:∀ j,q j ≤ k→(M*ᵥx) j=(M *ᵥ y) j): x i=y i:=by
    let z:=x-y; have hx :∀ n:ℕ,∀ j,q j<n → q j≤ k → z j=0:=by
        intro n; induction n with
        | zero=> intros; omega
        | succ n ih=>
          intro j hq hk
          apply (mul_eq_zero.mp ?_).resolve_left (zero_lt_one.trans_le (h.self j)).ne'
          have hv : (M *ᵥ z) j=0:=by unfold z; rw [mulVec_sub, Pi.sub_apply,hp j hk,sub_self]
          rw [← hv]; change M j j * z j=(∑ i,M j i*z i); apply Eq.symm; rw [Finset.sum_eq_single j]
          · intro i _ hh; by_cases u:q i<q j; · rw [ih i (by omega) (u.le.trans hk),mul_zero]
            rw [h.ties j i (by omega) hh.symm,zero_mul]
          simp
    exact sub_eq_zero.mp (hx (k+1) i (by omega) p)
namespace SolveCorner
variable {F':Frame G h}{S:SectionData F'}{M':SourceP F'} (a': Palette F' M' k u e X) (v':Chartage S A Ñ m c N k u e X)
abbrev proto (Y:Era G ℝ):=solve a' v' Y 0
variable {Y':Era G ℝ}(Z':Auth k Y')
include Z'
lemma aim (p0:r < i)(u':∀ r',r < r'→Y'.2 0 r'=0): let c':=proto a' v' Y';
     (∀ l,m≤l → l≤ c→(pier A Ñ N h k c l (Y'+rack F' M' c')).2 0 i=0) ∧ ∀ j:TagIx F' i, c' (eyeTag F' 0 e (Nat.zero_le _) j)=0:=by
    intro c'; let T:=Y'+rack F' M' c'; obtain ⟨D,H⟩:= billed F' e u k -- rewrite type
    have he(j t:ℕ)(w:When j t 0 i):Fruit 0 1 u (Y'.2 j t) 0:=by unfold When at w; rw [show j=0 by omega,u' t (by omega)]; exact Fruit.zero
    have hp(j t:ℕ)(w:When j t 0 i)(z:TagIx F' t): ‖row F' ((pier A Ñ N h k c m T).2 j t) z‖≤0:=by unfold When at w; rw [show j=0 by omega,output_at _ (Nat.zero_le e),show output F' _ _= _ from solve_target a' v' 0 Z']; exact norm_zero.le
    obtain ⟨h1,h2⟩:= H 0 (Nat.zero_le _) i S A Ñ m c N 0 X M' Y' c' 0 i (Nat.zero_le _) (Or.inr ⟨rfl,le_rfl⟩) le_rfl a' Z' v' he hp; simp_rw [mul_zero] at h1; exact ⟨fun i hi hx=>fruit_nil (h1 i hi hx),fun j=>norm_le_zero_iff.mp ((h2 (Nat.zero_le _) j).trans_eq (mul_zero _))⟩
-- projection at same rank of that whole term at K is ZERO, no tweaking neighbor slopes
lemma propped (p0:∀ i,r < i→Y'.2 0 i=0)(j:TagIx F' r) (l:ℕ)(hl:m≤l)(hc:l≤c): row F' ((pier A Ñ N h k c l (Y'+rack F' M' (proto a' v' Y'))).2 0 r)=0:=by
    let T:=Y'+rack F' M' (proto a' v' Y'); let t x:= pier A Ñ N h k c x T; have h0:Auth k T:= Z'.add (a'.mix _)
    induction hl with
    | refl=> funext i; rw [output_at _ (Nat.zero_le e),show output F' _ _= _ from solve_target a' v' 0 Z']; rfl
    | @step l hl ih=>
       have ht:m ≤ l:=hl
       have he (i : TagIx F' r):= a'.field i; have hp:= v'.pays l 0 r ht hc (Nat.zero_le _) ((fitsRank F' j).trans (v'.order.trans (Nat.le_add_right ..)))
       let V:=stepT S A Ñ l k N r; have hu: Auth k (t (l+1)):= piered v'.simple v'.ratios hc v'.cap h0
       obtain ⟨b',hT⟩:= attends hu 0 r u; have hw:= hp.back (t (l+1)) 0 b' hu le_rfl (by
           intro i f h; rcases h with e|⟨x,b⟩; exact False.elim (Nat.not_lt_zero i e); subst i; rw [show (t _).2 0 _= _ from (aim a' v' Z' b p0).1 (l+1) (by omega) hc]; exact Fruit.zero) hT
       apply (staff hp).inject (zero_le_one.trans v'.pos) h (fun i=> F'.bound _)
       have hi:=ih (show l≤c by omega); rw [pier_step v'.simple v'.ratios hc v'.cap h0] at hi
       change V *ᵥ _= V*ᵥ 0; rw [mulVec_zero]; funext i; exact ((sub_eq_zero.mp (norm_le_zero_iff.mp ((hw.1 i).trans_eq (mul_zero _)))).symm.trans (congr_fun hi i))
lemma basisLead (p0:∀ i,r < i→Y'.2 0 i=0)(i:TagIx F' r) (g:∀ j:TagIx F' r, wT F' j ≤ wT F' i → row F' (Y'.2 0 r) j= if i=j then 1 else 0) (j:TagIx F' r)(w:wT F' j≤ wT F' i): paper (proto a' v' Y') 0 (Nat.zero_le _) j= if i=j then -1 else 0:=by
   let L:=proto a' v' Y'; let V:= typus F' M' r; have he:= (a'.licensed (v'.ample.more ((fitsRank F' i).trans (v'.order.trans (Nat.le_add_right ..)))))
   have hh:= propped a' v' Z' p0 i c v'.length le_rfl; rw [pier_top] at hh; let x:=Y'+rack F' M' L
   have hf : before F' M' L 0 r=0:=by
       unfold before; refine Finset.sum_eq_zero (fun j hj=>?_); let a:= j.1; have H':=(Finset.mem_filter.mp hj).2; unfold lowerGrade at H'; have he : j.2.val=0 ∧ r< wr F' a:=by unfold a; omega
       have hv: j=eyeTag F' 0 e (Nat.zero_le _) (⟨a,rfl⟩:TagIx F' (wr F' a)):=Prod.ext rfl (Fin.ext he.1); rw [show L j=0 from (by rw [hv]; exact (aim a' v' Z' he.2 p0).2 _),zero_smul]
   have hw (j)(hj:wT F' j≤wT F' i): (V *ᵥ paper L 0 (Nat.zero_le _)) j=(V*ᵥ (-Pi.single i 1)) j:=by
       rw [← a'.price L, mulVec_neg, mulVec_single_one]; have hx:=axPlus (r:=r) Z' (a'.mix L) j (e:=0) -- type
       rw [a'.slim (r:=r) (e:=0) (Nat.zero_le e),hf, show (0:Era G ℝ).2 0 r=0 from rfl,zero_add] at hx
       change _= - V j i; rw [show V j i= _ from a'.high r j i hj]; by_cases h:j=i; · rw [if_pos h]; rw [g _ hj, if_pos h.symm] at hx; exact eq_neg_of_add_eq_zero_right (hx.symm.trans (congr_fun hh j))
       rw [if_neg h,neg_zero]; rw [g _ hj, if_neg (Ne.symm h),zero_add] at hx; exact hx.symm.trans (congr_fun hh j)
   rw [show paper _ _ _ j= _ from he.under j w hw]; by_cases h:j=i ; · simp [h]
   simp [h,Ne.symm h]
end SolveCorner
end YM.WilsonCoeffUV.Mer.Xa
