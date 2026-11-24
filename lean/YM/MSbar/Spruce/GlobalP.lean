import YM.MSbar.Spruce.Shove
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Spruce
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
open Lapaz
variable {G:Gauge}{c f:Side} {S:StepData c f}(F:Forest S.ratio)(R:Rep G f)(v:S.Choices)(J:Voice G)(Q:Palisade)(χ:ChartRatio G)
local notation "V"=>Primary c G
local notation "P0"=>Key F G
local notation "G!"=>Joint F G
local notation "T"=>Positions (Joint F G)
local notation "x!"=> Positions (Primary c G)
local notation "Ω"=> address F G
local notation "H"=>mold R F v
variable (X Y:Support f)(U':Config G f) (t:ℝ)(Z:Positions (Primary c G))
local notation "Λ"=> includeX (G:=G) F X
local notation "X₀"=>SpaceP F X G
local notation "χ!"=>(pinch (includeX (G:=G) F X) H)⁻¹
variable (e:PathData G)(l:Clip)(ρ:fieldDir G c 1→ AxisChart G F)
local notation "ν"=>vest (priced F v R.clip R.path) (t • Z)
local notation "f1"=>linCash F (t • Z)
open Next.SectorChange
local notation "I!"=>hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "r₀"=>rental F J R Y v (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "c!"=> sampleY F R v J X Y U' (t • Z)
local notation "A!"=> berth F R v J X Y U' Z t
variable {A B d C P D K w E:ℝ} (h:Suite J χ F X Y (postcard G c t Z) v R (vest (priced F v R.clip R.path) (t • Z)) A B d C P D (linCash F (t •Z)))
section
variable {ι σ τ: Type} [Fintype σ][DecidableEq σ] [Fintype ι][DecidableEq ι]
variable {A':Matrix ι ι ℝ}{M:Matrix σ σ ℝ}{x t a b u c1 r B1:ℝ}
local notation "π"=> PowerSeries.coeff
lemma inflation (l:σ→Site c)(i:ι→σ)(hp:Injective i)(z:Site c)(n:ℕ)(he:Dorian (l∘i) z a b n (show Matrix ι ι ℝ from A') r):Dorian l z a b n (extendM i A') r:=by
      let F:= extendM i A'; have hv(j k): F (i j) (i k)= A' j k:=congr_fun (congr_fun (embeds i hp A') j) k; have hZ(j k)(hj:j∉Set.range i ∨ k ∉ Set.range i):F j k=0:= squeezed i hj
      have hu (f:σ→ℝ)(he:∀ j,j∉ Set.range i→f j=0):∑ j,f j= ∑ j,f (i j):= by
           let X':=univ.image i; rw [show _= _ from (sum_subset (subset_univ X') (fun j _ h=>he j (by simpa [X',Set.range] using h))).symm,Finset.sum_image (fun j _ k _ he=>hp he)]
      refine ⟨he.positive,fun j=>?_,fun j=>?_⟩
      · change ∑ k, |F j k| *_ ≤ _; by_cases hj:j∈Set.range i
        · obtain ⟨p,rfl⟩:=hj; rw [hu]; swap; · intro k hk; rw [hZ _ _ (Or.inr hk),abs_zero,zero_mul]
          simp_rw [hv]; exact he.upper p
        simp_rw [fun k=> hZ j k (Or.inl hj), abs_zero,zero_mul,sum_const_zero]; exact mul_nonneg (Real.exp_pos _|>.le) he.positive
      change ∑ k, |F k j| *_ ≤ _; by_cases hj : j ∈ Set.range i
      · obtain ⟨p,rfl⟩:=hj; rw [hu]; swap; · intro k hk; rw [hZ _ _ (Or.inl hk),abs_zero,zero_mul]
        simp_rw [hv]; exact he.lower p
      simp_rw [fun k=> hZ k j (Or.inr hj), abs_zero,zero_mul,sum_const_zero]; exact mul_nonneg (Real.exp_pos _|>.le) he.positive
lemma defense {l:σ→Site c}(x:View σ) (a':ι→σ)(z:Site c) (n d p:ℕ)(h:Solver a' l a b c1 B1 p M)(hc:0≤a)(hb:0≤ b)(hp:‖x‖≤r)(hG:Injective a') (hD:∀ i:σ,i∉ Set.range a' → d ≤ separation (l i) z) (k:σ): let t:=Real.exp (-b*d)
      |((vanish a' M)*ᵥ x) k| ≤ (t * B1*r)*Eve b z (l k):=by
      intro t; let H':= vanish a' M; have hr:0 ≤ r:= (norm_nonneg _).trans hp; have ht:=vanSmall a' hG h.bids hD hb h.travels k; refine (abs_sum_le_sum_abs ..).trans (le_trans (b:=(∑ i,|H' k i| *liftW a p (separation (l k) (l i)))*r) ?_ ((mul_le_mul_of_nonneg_right ht hr).trans_eq ?_)); · rw [Finset.sum_mul]; exact sum_le_sum fun j _=> (abs_mul ..).trans_le (mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (w_start hc p _)) ((norm_le_pi_norm x j).trans hp) (abs_nonneg _) (mul_nonneg (abs_nonneg _) (wpos ..|>.le)))
      ring
end
variable {j p d' n m:ℕ}{r a b c1 C1 b' D':ℝ}
local notation "α'"=>Rolling.straight F G
local notation "d!"=> venue
variable (z:Site f)(hG:Solver (includeX (G:=G) F X) (address F G ∘ Sum.inr) a b C1 b' n (mold R F v))
lemma shrunk:Rolling.straight F G=imbed (Sum.inr:Key F G→Joint F G):=by
     let i:= (Sum.inr:Key F G→Joint F G); let BΞ:=Rolling.straight F G
     ext j k; let e:P0→ℝ:= Pi.single k 1
     have ht : imbed i *ᵥ e= BΞ *ᵥ e:=by
          unfold BΞ Rolling.straight; rw [LinearMap.toMatrix'_mulVec]; ext z; cases z with
          | inl z=> change _=0; exact inactive i _ (by simp [Set.range,i]) _
          | inr z=> exact congr_fun (shares i Sum.inr_injective _) z
     simpa only [BΞ,i,e,mulVec_single_one,Matrix.col,Matrix.transpose_apply] using congr_fun ht.symm j -- lemma?
variable (ha:0≤a)(hb:0≤b)(he:∀ i:Key F G,i ∉Set.range (includeX (G:=G) F X) → m ≤ separation (address F G ((Sum.inr i))) z)
local notation "T₀"=>Real.exp (-b*m)
local notation "G₀"=> (Real.exp (-b*m))*(b'*C1)
include he ha hb hG
lemma pitches: Gain Ω z a b n (Rolling.straight F G* (show Matrix (Key F G) (Key F G) ℝ from H⁻¹) * (Rolling.straight F G).transpose) (vene X F G * (show Matrix (Lake F X G) (Lake F X G) ℝ from χ!)* (vene X F G).transpose) C1 G₀:=by
    let i:= (Sum.inr:Key F G→Joint F G); let t:= includeX (G:=G) F X; let G' := H; have hZ:= realFuel t (secureY F X G) hG.bids (l:= Ω ∘ i) he ha hb hG.travels (hG.growth.low (le_add_of_nonneg_right hb)); unfold vene; rw [shrunk]; let w:Matrix (Lake F X G) (Lake F X G) ℝ:= (pinch t (mold R F v))⁻¹; let q:=extendM i (extendM t w); change Gain Ω z a b n (extendM i G'⁻¹) ((imbed i * imbed t)*w*(imbed i*imbed t).transpose) _ _; have hΔ : ((imbed i*imbed t)*w*(imbed i*imbed t).transpose) =q:= ?_; simp only [hΔ]
    swap; · unfold q extendM; simp only [transpose_mul,Matrix.mul_assoc,i,t]
    refine ⟨ha,hb,hZ.positive,reaching i Sum.inr_injective hG.growth,reaching i Sum.inr_injective hG.sealed,?_⟩
    let k:=extendM i (show Matrix (Key F G) (Key F G) ℝ from (G')⁻¹); let B:=extendM i (extendM t ((pinch t G')⁻¹)); change Dorian Ω z a b n (show Matrix _ _ ℝ from k-B) _
    rw [show k-B = extendM i ( (show Matrix _ _ ℝ from (G')⁻¹)- extendM t (pinch t G')⁻¹) from (by unfold k B extendM; rw [Matrix.mul_sub,Matrix.sub_mul])]; exact inflation Ω i Sum.inr_injective z n hZ
variable (hΩ:U'∈ hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z)) A B)(hX:X ⊆ Y) (hg:Critical F R.clip R.path ρ) (hR:ClassicalMatch F R.clip l R.path e ρ)(hp :S.patch.Branches S.kernel G) (hw:Premier (Rolling.main f R.clip R.path))(ht:0 < t)(hξ:Clear G J)
local notation "A'"=> berth F R v J X Y U' Z t
local notation "A0"=> berth F R v J X Y U' Z t 0
noncomputable def peg (t b A P:ℝ)(p:ℕ)(c:ℝ):=t⁻¹*( Real.exp (-b*p)*c*(P+A))
local notation "P'"=>peg t b A P m b'
include hΩ hX hg hR hp hw ht hξ h
lemma spreadP : 0 ≤ peg t b A P m b' ∧∀ i:Key F G, |A' 0 i-center F ρ Z i|≤ peg t b A P m b' * Eve b z (address F G (Sum.inr i)) := by
    let U:= outY J F Y (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z)) X f1 U'
    have hK:‖U‖ ≤ P+A:= Bakery.Film.frozen J F X Y _ U' ν χ hξ f1 h.seat hX hΩ
    let S':=(vanish Λ H)*ᵥ U
    have heq : A' 0 = center F ρ Z+t⁻¹• S':=by unfold berth;rw [Matrix.mulVec_zero,add_zero,loves F R v J X Y U' t Z e l ρ hp hw hg hR h.positivity ht,smul_add,inv_smul_smul₀ ht.ne']
    have hρ:= (norm_nonneg _).trans hK; have hh:=hG.hsize; refine ⟨?_,fun i=>?_⟩; · unfold peg; positivity
    rw [heq,Pi.add_apply,add_sub_cancel_left,Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr ht)]; exact (mul_le_mul_of_nonneg_left (defense U Λ z n m n hG ha hb hK (secureY F X G) he i) (inv_pos.mpr ht).le).trans_eq (mul_assoc ..).symm
lemma chanceP {η μ:SpringK (Joint F G)}(hK:Kind η)(ht': t≤1) (hℓ :∀ i≤p,Tokew (address F G) (a+b) n j 0 (PowerSeries.coeff i η) D'∧(PowerSeries.coeff i η).totalDegree ≤ j)(hr:∀ i≤p,Vault (address F G) {z} (a+b) n j 0 (PowerSeries.coeff i μ) D' ∧(PowerSeries.coeff i μ).totalDegree≤j)
      (hM:‖meetVar Z (A' 0)‖ ≤ r)(hN : ‖throne F ρ Z‖≤ r):
      |taste p (owes (Rolling.straight F G) (show Matrix (Key F G) (Key F G) ℝ from H⁻¹) η μ (throne F ρ Z) p) t -taste p (owes (vene X F G) ( (pinch Λ H)⁻¹) η μ (meetVar Z (berth F R v J X Y U' Z t 0)) p) t|≤ (p+1:ℕ)*( cardK p j C1 (D'*(1+r)^(j+1))*(G₀+peg t b A P m b')):=by
      obtain ⟨hu,hv⟩:=spreadP F R v J χ X Y U' t Z e l ρ h z hG ha hb he hΩ hX hg hR hp hw ht hξ
      have hx:∀ i:Joint F G,|throne F ρ Z i-meetVar Z (berth F R v J X Y U' Z t 0) i|≤ peg t b A P m b' * Eve b z (address F G i):=by
          intro i; cases i with
          | inr i=> change |center F ρ Z i- _|≤ _; rw [abs_sub_comm]; exact hv i
          | inl i=> change |Z i-Z i|≤ _; rw [sub_self,abs_zero]; exact mul_nonneg hu (Real.exp_pos _|>.le)
      exact joker _ _ hK (hG.bids.submatrix (secureY F X G) |>.inv) hG.bids.inv (pitches F R v X z hG ha hb he) hN hM hu hx hℓ hr ht.le ht'
end YM.MSbar.Spruce
