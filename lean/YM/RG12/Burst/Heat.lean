import YM.RG12.Burst.Fuel
import YM.RG12.Burst.Rich
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters Blaze.March
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "Z" => N.conduit
local notation "cR" => Q.costs L μ R.beta x q

-- rescaled ingress readiness. Before θ.W. uniform in call-world.
open PhysicalNext.Repeat.Height
local notation "Ξ" => N.conduit
local notation "sf" => grow G L x
local notation "wo" => Q.mark L μ x
local notation "m11" => mail11 (S:=S) (L:=L) (x:=x) M
/-- RISK combined, ALL optional and packet penalties through both tree currencies. Not claiming magnitude of true costs grows when stance of one barcode occurs. Some purposes(residual E projection effects) need additional spatial costs appended. This currency asks just on \sup criterion & projections. -/
def dose (s:ℝ)(p:H.fragrances):ℝ:= s^hue H p * sf^acme H p*Real.exp (wo * Height.overlap H p)
lemma milk11 (p:H.fragrances) : clusters H.seam (blue M H N (s:=s)) p.2= dose H s p * red1 M H N p:=by
   unfold dose acme Height.overlap red1 clusters blue risk Height.gust
   simp only [prod_mul_distrib,prod_pow_eq_pow_sum,Nat.cast_sum,mul_sum,Real.exp_sum,hue]; ring
lemma massive11 (p:H.fragrances)(hs:1 ≤ s)(hg:1≤ grow G L x) : 1 ≤ dose H s p:= by
   have hV:= H.laws.acquired.marked
   unfold dose; refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs) (one_le_pow₀ hg)) (Real.one_le_exp (mul_nonneg ?_ (Nat.cast_nonneg _))); exact hV
local notation "t!" => Q.goal L x+ value10 Q L μ x s B j n
lemma salty (hv:Bikes Q L μ x a E B j n)(hr: Ready H.smallAt (radiusB x) (blue M H N (s:=s)) (a+E) t! E (1/2)):
    Ac.Hit (fun i:H.fragrances=> H.bookFoot (.inr i)) (radiusB x) (fun i=> dose H s i * red1 M H N i) (a+E) ((t!) * (1-(1/2):ℝ)⁻¹):=by
    intro i
    have h:=log_hit_tail H.seam H.smallAt (radiusB x) H.testS hr (add_nonneg hv.posts hv.allow.le) 0 i; rw [pow_zero,mul_one] at h
    convert! h using 2; rename_i p; dsimp only
    simp_rw [← milk11 M H N (p:=p)]
    unfold currency; change (if i∈unionOf H.smallAt p.2 then _ else _)=(if _ then _ else _); simp; rfl
local notation "w!" i => paint10 Q L μ x s B j n E i
local notation "Z!" => locus M H
local notation "de" => (m11*d0)
lemma front11 (hs:1≤ s)(hg:1≤ grow G L x)(hv:Bikes Q L μ x a E B j n)(hr:Ready H.smallAt (radiusB x) (blue M H N (s:=s)) (a+E) t! E (1/2)) {y:Site c}(hy:y∈M.crest.image S.ratio.parent)(i:ℕ):
    SumBudget (fun p:H.fragrances=> dose H s p*(rib11 M H N y i p)*Real.exp (a*coverNumber (radiusB x) (Z! y p))) (de*w! i):=by
    have H':= salty M H N hv hr y
    have hQ:=mintN M (S:=S) hg; have he' (p:H.fragrances):=massive11 H p hs hg; have hD:=(mul_nonneg (zero_le_one.trans hQ) (dew M H|>.2.1))
    have he:=hv.allow
    have hC:0 ≤ collars G E x j i:=by unfold collars Reserves.polyPrice March.shiftG; positivity
    let t:= Q.goal L x+value10 Q L μ x s B j n
    change SumBudget _ (de*(collars G E x j i*(t*(1-(1/2))⁻¹))); rw [← mul_assoc de]
    refine budget_mono (budget_scale (mul_nonneg hD hC) H') (fun p=> by exact mul_nonneg (mul_nonneg (zero_le_one.trans (he' _)) (ribN M H N hg y _)) (Real.exp_pos _).le) fun p=> ?_
    unfold rib11; split
    next hh =>
      have hp:=seatY M H y hy p; unfold locus at hp; rw [if_pos hh] at hp
      dsimp only; rw [if_pos hp]; unfold potY locus collars flareC; rw [if_pos hh, mul_pow]
      let t:ℝ:=coverNumber (radiusB x) (H.bookFoot (.inr p)); let k := i*j -- power! check flareC
      have hG:=polynomial_cost he (show 0≤t from Nat.cast_nonneg _) k
      have hL : 0≤ dose H s p*(de*red1 M H N p)*(March.shiftG x)^k*Real.exp (a*t):=by unfold March.shiftG; have ho:= redN M H N hg p; have hd:= he' p; positivity
      change dose H s p * (de*red1 M H N p*((March.shiftG x)^k*(1+t)^k))*Real.exp (a*t) ≤ (de*((March.shiftG x)^k*_))*(dose H s p*red1 M H N p*Real.exp ((a+E)*t)) -- confirm
      calc
        _ = (dose H s p*(de*red1 M H N p)*(March.shiftG x)^k*Real.exp (a*t))*(1+t)^k :=by ring
        _ ≤ (dose H s p*(de*red1 M H N p)*(March.shiftG x)^k*Real.exp (a*t))*(E⁻¹^k * k.factorial*Real.exp E*Real.exp (E*t)) :=mul_le_mul_of_nonneg_left hG hL
        _ = _:=by rw [add_mul,Real.exp_add]; unfold Reserves.polyPrice; ring
    next hh=> rw [mul_zero,zero_mul]; exact (budget_scale (mul_nonneg hD hC) H').1 p
-- wanted Penalty11, relative to mark ticket. Define cold H l references r.live.logkey even if cold wing. NOT Dried analyzer.
def cold (w:Wing)(p:H.fragrances):Prop := (3≤hue H p ∨ Height.overlap H p≠0)∨ acme H p ≥ sign11 (w.badge S)+1 ∧ 2≤hue H p
variable (hs:1≤ s)(hg:1≤ grow G L x)
include hs hg
lemma budget11 (ho:s*grow G L x ≤ Real.exp (Q.mark L μ x))(hr:grow G L x≤ s)(i:H.fragrances)(hi:cold H M.turn i)(hval:speaks M H i) :
    (s^2*grow G L x)*m11 ≤ dose H s i:=by
   let k:=sign11 (M.turn.badge S)
   have hK:k ≤ acme H i:=by
     obtain ⟨j,hj,-⟩:= hval; have hh:k≤pins S (i.2 j).val:= Finset.single_le_sum (s:=(i.2 j).val) (f:=fun j=>sign11 j) (fun _ _=> Nat.zero_le _) hj
     exact hh.trans (Finset.single_le_sum (f:=fun j=> pins S (i.2 j).val) (fun _ _=>Nat.zero_le _) (mem_univ j))
   let h':=i.2 none; have hS(i:H.ThinP):1≤ i.val.card:= Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (by
      obtain ⟨u,ht⟩:= i.2.1; intro hh; change u∈ i.val.biUnion H.supportP at ht; rw [hh] at ht; simp at ht))
   have he:1 ≤ hue H i:= (hS h').trans (Finset.single_le_sum (s:=univ) (f:=fun j=>(i.2 j).val.card) (fun _ _=>by simp) (mem_univ none))
   set g:=grow G L x
   have hp:0 ≤ Q.mark L μ x:= H.laws.acquired.marked
   have hx:=mul_nonneg hp (Nat.cast_nonneg (α:=ℝ) (Height.overlap H i)); have hV(g' h':ℕ) (hr:h'≤ hue H i)(he:g'≤ acme H i)(j':ℝ) (hg':0≤j')(hl:j' ≤ Real.exp (Q.mark L μ x*Height.overlap H i)): s^h'*g^g' * j'≤ dose H s i:=by
      unfold dose; exact mul_le_mul (mul_le_mul (pow_le_pow_right₀ hs hr) (pow_le_pow_right₀ hg he) (by positivity) (by positivity)) hl hg' (by positivity)

   rcases hi with (ht|ht)|⟨hi,hf⟩
   · have hh:=hV k 3 ht hK 1 zero_le_one (Real.one_le_exp hx); change s^2*g*g^k ≤ _; rw [mul_one] at hh; exact (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hr (sq_nonneg s)).trans_eq (by ring)) (pow_nonneg (zero_le_one.trans hg) _)).trans hh -- equality implicit expected type? _
   · unfold mail11; have h:=hV k 1 he hK (s*g) (by positivity) (ho.trans (Real.exp_monotone (le_mul_of_one_le_right hp (show (1:ℝ) ≤ Height.overlap H i by exact_mod_cast (show (1:ℕ)≤ Height.overlap H i from Nat.pos_of_ne_zero ht)))))
     exact (show (s^2*g)*g^k = s^1*g^k*(s*g) from by ring).trans_le h
   have hh:=hV (k+1) 2 hf hi 1 zero_le_one (Real.one_le_exp hx); exact (show s^2*g*g^k=s^2*g^(k+1)*1 from by rw [pow_succ]; ring).trans_le hh

local notation "cost11"=> (s^2* sf)⁻¹
lemma spent (ho:s*grow G L x ≤ Real.exp (Q.mark L μ x))(hl:grow G L x ≤ s)(hv:Bikes Q L μ x a E B j n)(hr:Ready H.smallAt (radiusB x) (blue M H N (s:=s)) (a+E) t! E (1/2)){y:Site c}(hy:y∈M.crest.image S.ratio.parent)(i:ℕ):
   SumBudget (fun p:H.fragrances=> if cold H M.turn p then rib11 M H N y i p*Real.exp (a*coverNumber (radiusB x) (Z! y p)) else 0) (cost11 *d0*w! i) :=by
   have hJ:=zero_lt_one.trans_le (mintN M (S:=S) hg); let k:=(s^2* sf)*m11; have hk:0<k:=by unfold k; positivity
   have hh:=budget_scale (inv_pos.mpr hk).le (front11 M H N hs hg hv hr hy i)
   rw [show k⁻¹ * (de*(w! i))= cost11 * d0*(w! i) from ?_] at hh; swap; · unfold k; field_simp
   have hz (p:H.fragrances):0≤ rib11 M H N y i p * Real.exp (a * coverNumber (radiusB x) (Z! y p)):= mul_nonneg (ribN M H N hg y p) (Real.exp_pos _).le
   refine budget_mono hh (fun p=>?_) fun p=> ?_
   · split; exact hz p; rfl
   split
   next h=>
     rw [mul_assoc (dose ..),←mul_assoc]; by_cases hx:speaks M H p
     · exact le_mul_of_one_le_left (hz p) ((one_le_inv_mul₀ hk).mpr (budget11 M H hs hg ho hl p h hx))
     rw [rib11,if_neg hx,zero_mul,mul_zero]
   next h=> exact hh.1 _
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12
