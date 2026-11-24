import YM.FVA2.Repair
/-!
# Reading after a formal clock inverse. Jet continuity
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Elegant
open Function Filter Set MeasureTheory PositionX
open Pert Pert.Position Maxwell Maxwell.Free PositionX.Bare.Shop PositionX.Jet
open PositionX.Ribbon PositionX.Detector
open scoped Topology ContDiff BigOperators Classical
variable {I X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{l:Filter I}
variable {f:I→Word X}{x: Word X}{p:I→ Word ℝ}{a:Word ℝ}
lemma powersAt (h:TurnsOn l f x)(HE:TurnsOn l p a): TurnsOn l (fun i=>ren ( p i ) ( f i )) (ren a x):= by
   intro i; unfold ren order; exact Tendsto.const_smul (tendsto_finsetSum _ (fun j _=> ( tendsto_finsetProd _ (fun k _=> ( HE _ ).const_mul _)).smul ( ( h _ ).const_smul ( j.length.factorial:ℝ )) )) _
open PowerSeries
open MS.Book MS.Book.Convolve MS.Book.Program
open Clock Score Attend WorldJet
-- scalar algebra: ren invoice recurrence. diagonal power n. use complex proof.
def symbol (v:Word ℝ): Cn:= PowerSeries.mk ( Complex.ofReal ∘ v )
lemma α_eq (x:Word ℝ)(i:ℕ) : Clock.out (symbol x) i= x i:= Clock.out_coeff _ _|>.trans (coeff_mk ..)
lemma bill_q (x:Word ℝ)(i:ℕ) : coeff i (symbol x)=x i:= coeff_mk ..
lemma litK (h:light a) : Rooted (symbol a):= (bill_q ..).trans (show ((a 0:ℝ):ℂ)=0 from by rw [h,Complex.ofReal_zero])
lemma ageT {u:Cn}(h:Rooted u)(i:ℕ): cut u i i=(coeff 1 u)^i := by -- induction
   induction i with
   | zero=> simp [Program.cut]
   | succ i ih=> unfold Program.cut; rw [pow_succ,pow_succ,coeff_mul,Finset.sum_eq_single (i,1) ]; · exact congr_arg (·*_) ih
                 · intro j hj he; obtain hx:= Finset.HasAntidiagonal.mem_antidiagonal.mp hj; by_cases hV:j.2=0; rw [hV,h,mul_zero]; have ht:j.1 < i:= by_contra (fun hx=> he (Prod.ext (by dsimp; omega) (by dsimp; omega))); rw [show coeff j.1 (u^i)=0 from Program.blocked h ht,zero_mul]; -- finset instance
                 simp
lemma renReal (b:Word ℝ) (hp:light a) (d:ℕ) : (↑(ren a b d: ℝ): ℂ)= ∑ i∈ Finset.range (d+1),Program.cut (symbol a) i d*( b i:ℂ ):= by
   let X:ℝ→ₗ[ℝ]ℂ:= Complex.ofRealCLM.toLinearMap; rw [show (↑(ren a b d: ℝ): ℂ)= ren a (Clock.out (symbol b)) d from ?_ ]; swap; · rw [show Clock.out _= X ∘ b from funext ( α_eq b ) ]; exact congr_fun ( ren_writes X a b ) d
   rw [ ← WorldJet.ref_frame a hp (symbol b) (symbol a) (funext fun i=> (α_eq a i).symm),gradeS,rules, show Finset.Iic d=Finset.range (d+1) by ext i; simp]; simp_rw [α_eq ]; rfl
private lemma hours (hh:Genuine a)(n:ℕ) : (Jet.inverse a n:ℂ)=( ( (a 1:ℝ):ℂ )^n)⁻¹ * ((headway n:ℂ) - ∑ i∈ Finset.range n,Program.cut (symbol a) i n * (Jet.inverse a i:ℂ) ):= by
    have hp:= congr_arg Complex.ofReal (congr_fun ( headback hh ) n ); rw [renReal _ hh.1 n, Finset.sum_range_succ, ageT (litK hh.1), bill_q] at hp; rw [← hp]; field_simp [show ((a 1):ℂ)≠0 from by exact_mod_cast hh.2]; ring
private lemma cutoff (hm:TurnsOn l p a)(i j:ℕ): Tendsto (fun t=>Program.cut (symbol (p t)) i j) l (𝓝 (Program.cut (symbol a) i j)):= by
   induction i generalizing j with
   | zero=> unfold Program.cut; simp only [pow_zero]; exact tendsto_const_nhds
   | succ k ih=> unfold Program.cut; simp_rw [pow_succ,coeff_mul]; refine tendsto_finsetSum _ (fun i _=> (ih i.1).mul ?_ ); simp_rw [bill_q ]; exact Complex.ofRealCLM.continuous.continuousAt.tendsto.comp (hm _)
lemma inverting (hm:Genuine a)(h:TurnsOn l p a)(hs:∀ᶠ i in l,light (p i)): (∀ᶠ i in l,Genuine (p i)) ∧ TurnsOn l ( Jet.inverse ∘ p ) (Jet.inverse a) := by
   have ht:= (h 1).eventually (isOpen_ne.mem_nhds hm.2); -- name
   have hv: ∀ᶠ i in l,Genuine (p i):= hs.and ht; refine ⟨hv,?_⟩; intro n; suffices H:Tendsto (fun i=>Complex.ofReal ( (inverse ∘ p) i n )) l (𝓝 (Complex.ofReal (inverse a n))) from Complex.reCLM.continuous.continuousAt.tendsto.comp H; induction n using Nat.strong_induction_on with
   | h k ih=>
       rw [hours hm]; refine (show Tendsto _ _ _ from Tendsto.mul ( f:=fun t=>(( (p t 1:ℝ):ℂ)^k)⁻¹ ) ?_ (tendsto_const_nhds.sub (tendsto_finsetSum _ (fun i hi=> (cutoff h i k).mul (ih i (Finset.mem_range.mp hi)))) ) ).congr' ?_;
       · exact ((( Complex.ofRealCLM.continuous.continuousAt.tendsto.comp (h 1)).pow k)).inv₀ (pow_ne_zero _ (by change ((a 1:ℝ):ℂ)≠0; exact_mod_cast hm.2)) -- inference map type
       exact hv.mono fun i hi=> (hours hi k).symm
end YM.FVA2.Elegant
