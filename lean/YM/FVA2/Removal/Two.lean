import YM.FVA2.Arrival.Net
/-!
 # Uncompressed period dependence of regulator-removal estimates

 Preparations for the FVA₂ strengthening in `Platter`. Stop requiring `Tide.Super` to apply quantitative estimates. Permit
 ***any*** dependence between side lengths and positive mesh sizes. mesh size still eventually
 small (use `comap P.θ atTop` to enforce over an arbitrary whole collection of points/periods;
 key finiteness condition this buys is stencil separation **on the lattice cover**), size errors
 then not claimed small unless a schedule is specified. `Vol` uses the stronger period factor
 in N lattice-space units, see also `Vol.hard` for cost in physical side length.

 We expose the two auxiliary parts of the error underlying `YM.MS`: inversion finite quotient
 vs cover (both *before and after* any source-generator undoing, but see specific orientation),
 and then cover vs physical continuum. Thus `MenuCost.reaches` comparison gives $C a^ξ+C a^{-m}ℳ^{-α}$
 for all joint regulators here with the specified `Fit` (see `tabulate` in Platter), and undoing the price generator (physical vs transformed
 columns) costs just the period part. The quantitative MS estimate extends `Tide` to control the orbital
 remainder on admissible schedules.
 Derivative norms supplied separately.

 DO NOT require a bound on side from above, since we have a margin to pay log costs with part
 of the power. Even no lower-growth requirement for this statement. In particular at deliberately
 small periods relative to the spacing-related scale the remainder is NOT proved small. Not
 claiming clearance of marks *on quotient* then (see `Fit`
 for the actual positioning, separation-of-offsets and clearance requirements). Prove smallness on the stipulated super-poly schedule. Not taking the
 limit of any bare D matrix beyond its leading as a hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Removal
open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.Koszul MS.Plane MS.Landau MS.Tone Lattice MS.Land MS.Latch MS.Latch.Job MS.Tide MS.High
open MS.Vane MS.Rake MS.Rake.Geo MS.Vista MS.Vane MS.Fleet MS.Dial
open scoped Topology ContDiff Interval
variable {I:Type} {l:Filter I}{P:Geo I}{L:I→Side}{V: MS.Vista.Visa I}{μ:ℝ}
-- no limit at all on side for Warrant. Always construct with explicit bank exp(θ)*(1+|μ|).
def loose (P:Geo I)(μ:ℝ) : MS.Vista.Visa I:= ⟨ fun i=> exp (P.θ i)*(1+|μ|), fun i=> one_le_mul_of_one_le_of_one_le ( Real.one_le_exp ( P.room i ) ) (by simp) ⟩
lemma extent {W:Type}{c:Berth ( W:=W ) ( I:=I )} (v:Profile P c)(H:∀ i,P.η i=μ-P.θ i): WidthW (loose P μ) P.η c := by
 let B(i:I):= exp (P.θ i)*(1+|μ|); have hv(i:I):exp (P.θ i)≤B i:= le_mul_of_one_le_right (exp_pos _|>.le) (by simp)
 refine ⟨ fun i=>?_,fun i=>?_⟩; · rw [H]; change 1+|μ-P.θ i|≤B i; obtain ht:= Real.add_one_le_exp ( P.θ i ); obtain hb:=abs_sub μ ( P.θ i ); rw [abs_of_nonneg ( P.room _ )] at hb; unfold B; nlinarith [abs_nonneg μ,Real.one_le_exp ( P.room i )]
 obtain ⟨a,ha,hA⟩:= v i; refine ⟨ a,ha,1,fun x=>?_⟩; rw [Pi.one_apply,pow_one,mul_one]; exact (hA x).trans (mul_le_mul_of_nonneg_left (hv x) ha.le)
@[simp] lemma pays (P:Geo I)(μ:ℝ)(i:I): ( loose P μ ).bank i=exp ( P.θ i )*(1+|μ|):= rfl
variable (P L)
/-- price functions use log variable $θ=log(1/a)$ and N=actual side lattice count. -/
def vol (m:ℕ)(i:I): ℝ:= exp ((m:ℝ)*P.θ i)*(tickA L i)^(-mildG)
def phys (i:I):ℝ:= exp (-P.θ i)*tickA L i
def cost (m:ℕ)(i:I): ℝ:= lake P mildG i+vol P L m i
variable {P L}{x y u v:I→ℂ}
/-- pure volume part -/
def Vol (l:Filter I)(P:Geo I)(L:I→Side)(f:I→ℂ): Prop:= ∃ C:ℝ,0<C∧∃ m:ℕ,∀ᶠ i in l, ‖f i‖≤ C*vol P L m i
/-- finite sums/products carry this cost; no need assume the period part is bounded. -/
def Total (l:Filter I)(P:Geo I)(L:I→Side)(f:I→ℂ): Prop:= ∃ C:ℝ,0<C∧∃ m:ℕ,∀ᶠ i in l, ‖f i‖≤ C*cost P L m i
lemma phys_p (P:Geo I)(L:I→Side)(i:I):0<phys P L i:= mul_pos (exp_pos _) (δ_p ..)
lemma toPhysical (P:Geo I)(L:I→Side)(m:ℕ)(i:I): vol P L m i ≤ exp ((m:ℝ)*P.θ i) * ( phys P L i ) ^ (-mildG):= by
 unfold vol; apply mul_le_mul_of_nonneg_left _ (exp_pos _|>.le); apply Real.rpow_le_rpow_of_nonpos (phys_p ..) _ (neg_nonpos.mpr mild_p.le); exact mul_le_of_le_one_left (δ_p L i|>.le) ( exp_le_one_iff.mpr ( neg_nonpos.mpr ( P.room i ) ) )
lemma money (P:Geo I)(L:I→Side)(m:ℕ)(i:I): 0 < vol P L m i := mul_pos (exp_pos _) ( rpow_pos_of_pos ( δ_p L i ) _ )
lemma rise (P:Geo I)(L:I→Side){m n:ℕ}(h:m≤n)(i:I): vol P L m i≤ vol P L n i:= mul_le_mul_of_nonneg_right (exp_monotone (mul_le_mul_of_nonneg_right ( by exact_mod_cast h ) (P.room i))) ( Real.rpow_pos_of_pos (δ_p L i) _|>.le )
lemma volle (P:Geo I)(L:I→Side)(m n:ℕ)(i:I): vol P L m i* vol P L n i ≤ vol P L (m+n) i:= by
 unfold vol; push_cast; rw [mul_mul_mul_comm, ←exp_add,add_mul]; apply mul_le_mul_of_nonneg_left _ (exp_pos _|>.le); apply mul_le_of_le_one_right ( Real.rpow_pos_of_pos (δ_p L i) _|>.le ); exact Real.rpow_le_one_of_one_le_of_nonpos (δ_L L i) (neg_nonpos.mpr mild_p.le)
lemma cost_p (P:Geo I)(L:I→Side)(m:ℕ)(i:I): 0<cost P L m i:= add_pos (exp_pos _) ( money .. )
lemma advance (P:Geo I)(L:I→Side){m n:ℕ}(h:m≤n)(i:I): cost P L m i≤ cost P L n i:= add_le_add_right (rise P L h i) _ -- add on left Lean?
lemma engl (P:Geo I)(i:I): lake P mildG i ≤ 1:= exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr mild_p.le) (P.room i))
lemma cost_mul (P:Geo I)(L:I→Side)(m n:ℕ)(i:I): cost P L m i*cost P L n i ≤ 3*cost P L ( m+n ) i:= by
 have hL : 0≤ lake P mildG i:= exp_nonneg _; have hm:0≤ vol P L m i:= money .. |>.le; have hn:0≤ vol P L n i:= money ..|>.le; have h:= engl P i; unfold cost; rw [add_mul,mul_add,mul_add]; have hv:= rise P L ( show m≤m+n from (by omega) ) i; have he:= rise P L ( show n≤m+n from (by omega)) i; linarith [ volle P L m n i, mul_le_of_le_one_left hn h,mul_le_of_le_one_right hm h,mul_le_of_le_one_left hL h ]
lemma Vol.plus (a: Vol l P L x)(b: Vol l P L y): Vol l P L ( x+y ):= by
 obtain ⟨C,hC,m,hm⟩:=a; obtain ⟨D,hD,n,hn⟩:=b; refine ⟨ C+D,by positivity,m+n,?_⟩; filter_upwards [hm,hn] with i hm hn; apply le_trans (norm_add_le _ _); rw [add_mul]; exact add_le_add (hm.trans (mul_le_mul_of_nonneg_left (rise P L (by omega) i) hC.le)) (hn.trans (mul_le_mul_of_nonneg_left (rise P L (by omega) i) hD.le)) -- inference PI
lemma Vol.neg (a:Vol l P L x): Vol l P L (-x):= by simpa [ Vol ] using a
lemma Vol.sub (a:Vol l P L x)(b:Vol l P L y): Vol l P L (x-y):= sub_eq_add_neg x y |>.symm ▸ a.plus b.neg
lemma Vol.zero : Vol l P L 0 := ⟨ 1,zero_lt_one,0, Eventually.of_forall (fun i=> by simp [ money P L 0 i|>.le ]) ⟩
lemma Vol.restrict (p:Vol l P L x)(h:x =ᶠ[l] y): Vol l P L y:= by obtain ⟨C,hC,m,k⟩:=p; refine ⟨ C,hC,m,?_⟩; filter_upwards [h,k] with i hi hn; rwa [←hi]
lemma Vol.covers (p:Vol l P L x): Total l P L x:= by
 obtain ⟨C,hC,i,hi⟩:=p; exact ⟨ C,hC,i,hi.mono fun x hx=> hx.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (exp_pos _|>.le)) hC.le) ⟩
lemma Vol.high (p:Vol l P L x)(d:ℕ) : Vol l P L ( higher P d * x ):= by
 obtain ⟨C,hC,m,hM⟩:=p; refine ⟨ C,hC,d+m,hM.mono (fun i hi=> ?_) ⟩; rw [Pi.mul_apply, norm_mul, high_nn]; refine (mul_le_mul_of_nonneg_left hi (exp_pos _|>.le)).trans_eq ?_; unfold vol; push_cast; rw [add_mul,Real.exp_add]; ring
lemma Total.plus (a: Total l P L x)(b: Total l P L y): Total l P L ( x+y ):= by
 obtain ⟨C,hC,m,hm⟩:=a; obtain ⟨D,hD,n,hn⟩:=b; refine ⟨ C+D,by positivity,m+n,?_⟩; filter_upwards [hm,hn] with i hm hn; apply le_trans (norm_add_le _ _); rw [add_mul]; exact add_le_add (hm.trans (mul_le_mul_of_nonneg_left (advance P L (by omega) i) hC.le)) (hn.trans (mul_le_mul_of_nonneg_left (advance P L (by omega) i) hD.le))
lemma Total.neg (a:Total l P L x): Total l P L (-x):= by simpa [ Total ] using a
lemma Total.alt (p:PeakT l P mildG x): Total l P L x:= by
 obtain ⟨C,hC,i⟩:=p; refine ⟨ C,hC,0,i.mono fun i hi=>?_⟩; exact hi.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (money ..|>.le)) hC.le)
lemma Total.combine (p:Total l P L x)(q:Total l P L y): Total l P L (x*y):= by
 obtain ⟨C,hC,m,hm⟩:=p; obtain ⟨ D,hD,n,hn ⟩:=q; refine ⟨3*(C*D),by positivity,m+n,?_⟩; filter_upwards [hm,hn] with i hp hq; rw [Pi.mul_apply,norm_mul]; apply (mul_le_mul hp hq (norm_nonneg _) ((norm_nonneg _).trans hp) ).trans; rw [mul_mul_mul_comm]; refine (mul_le_mul_of_nonneg_left (cost_mul P L m n i) (by positivity : 0≤ C*D)).trans_eq ?_; ring
lemma Total.ticket (p:Total l P L x)(q:PeakT l P 0 y): Total l P L (x*y):= by
 obtain ⟨C,hC,m,hm⟩:=p; obtain ⟨ D,hD,hn ⟩:=q; refine ⟨C*D,by positivity,m,?_⟩; filter_upwards [hm,hn] with i hp hq; rw [Pi.mul_apply,norm_mul]; simp [lake] at hq; apply (mul_le_mul hp hq (norm_nonneg _) ((norm_nonneg _).trans hp) ).trans; refine le_of_eq ?_; ring
-- products with bounded targets but fees possibly much bigger at early errors.
def Tight (l:Filter I)(P:Geo I)(L:I→Side)(x y:I→ℂ): Prop:= PeakT l P 0 y∧ Total l P L (x-y)
lemma Tight.plus (a:Tight l P L x y)(b:Tight l P L u v): Tight l P L (x+u) (y+v):= by refine ⟨ a.1.plus b.1,?_⟩; rw [ add_sub_add_comm ]; exact a.2.plus b.2
lemma Tight.join (a:Tight l P L x y)(b:Tight l P L u v): Tight l P L (x*u) (y*v):= by
 refine ⟨ by simpa using a.1.mul b.1,?_⟩; let H:= (a.2.ticket b.1).plus ((b.2.ticket a.1).plus (a.2.combine b.2)); -- Prop synthetic
 rw [ show x*u-y*v=(x-y)*v+( (u-v)*y+(x-y)*(u-v)) from (by ring) ]; exact H
lemma Tight.constant (x:ℂ): Tight l P L (fun _=>x) (fun _=>x):= by refine ⟨ ((PeakT.always (l:=l) (P:=P) (x:=mildG) x)).1, ?_⟩; rw [sub_self]; exact Vol.zero.covers
end YM.FVA2.Removal
