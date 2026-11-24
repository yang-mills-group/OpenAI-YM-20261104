import YM.GradedFar.Growth.Chair

/-!
# QScale upper range

Notation interval lengths = log T factors (positive! feed **negative** to K).
-/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open O O.Score O.Enh
open Continuation
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d : ℕ} {C B : ℝ} {I J : Type}
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=> gYM G

structure Loft (G : Gauge) (I : Type) where
  path : Filter I
  r : I→ℝ
  C : ℝ
  C0 : 0<C
  B : ℝ
  B0 : 0<B
  nearing : Tendsto r path τ
namespace Loft
variable (b : Loft G I)
def height (i : I):=log (b.C * g (b.r i)^(-b.B))
variable (simple : G.Simple)
include simple
local notation "T"=>b.height
lemma climbs : Tendsto T b.path atTop := by
  apply tendsto_atTop.mpr; intro x
  filter_upwards [b.nearing.eventually (has_room simple b.C b.B b.C0 b.B0 (exp x))] with i h
  have ht:= h.trans' (exp_pos x).le; unfold height
  rw [← log_exp x]; gcongr
lemma limit : ∀ᶠ i in b.path, (b.r i,b.height i) ∈ band G b.C b.C b.B := by
  filter_upwards [b.nearing.eventually (positive_g simple)] with i hi
  have hh : exp (b.height i)=_ := exp_log (show 0<b.C * g (b.r i)^(-b.B) from mul_pos b.C0 (by positivity))
  exact ⟨le_of_eq hh, le_of_eq hh.symm⟩
lemma path_loft : Tendsto (fun i=>(b.r i,b.height i)) b.path (Window.windows (band G b.C b.C b.B)) :=
  tendsto_inf.mpr ⟨Filter.Tendsto.prodMk b.nearing (b.climbs simple), tendsto_principal.mpr (b.limit simple)⟩
def board : Board I where
  l:=b.path
  s:=b.height
  «g»:=gYM G ∘ b.r
  spacious := b.climbs simple
  shrinking := (shrink simple).comp b.nearing
  positive := b.nearing.eventually (positive_g simple)

abbrev Mid (b : Loft G I) (s : I → ℝ) := ∀ᶠ i in b.path,0 ≤ s i ∧ s i ≤ b.height i
theorem eventual_power {p q : ℕ} {a : ℝ} (h : q < p + b.B*a)
    (k : ℕ) (c : ℝ) (hc : 0<c): -- post a s means exp(-a*logT); cutoff T=g^-B, cost g^(B*a).
    ∀ᶠ i in b.path, c*g (b.r i)^p*post a (b.height i) k ≤ g (b.r i)^q := by
  filter_upwards [(b.path_loft simple).eventually (Stretch.trade simple b.C0 b.C0 b.B0
    (b:=(q:ℝ)) (a:=(p:ℝ)) (p:=-a) (q:=0) (by linarith only [h]) k hc),b.nearing.eventually (positive_g simple)] with i hi hi'
  unfold post; rw [mul_comm (-a),exp_mul]; rw [Real.rpow_natCast,Real.rpow_natCast,rpow_zero,mul_one] at hi
  nlinarith only [hi]
lemma soon {s : I → ℝ} (h : b.Mid s) : Tendsto (fun i=> b.r i*exp (s i)) b.path τ := by
  have hr : ∀ᶠ i in b.path, 0 < b.r i:= b.nearing.eventually self_mem_nhdsWithin
  have hu : ∀ᶠ i in b.path,0<b.r i*exp (s i) := hr.mono fun _ hi=> mul_pos hi (exp_pos _)
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,hu⟩
  have hh := ((shrink simple).comp b.nearing).const_mul b.C
  rw [mul_zero] at hh; refine squeeze_zero' (hu.mono fun i hi=>hi.le) ?_ hh
  filter_upwards [b.nearing.eventually (Stretch.small_root simple (b.B+1)),b.limit simple, (b.board simple).positive, h,hr] with i hi ⟨hw,_⟩ (hg : 0 < g (b.r i)) hs hp
  let t:= g (b.r i); have hg' : 0<t:=hg
  change b.r i * exp (s i) ≤ b.C*t
  calc
    _ ≤ t^(b.B+1)*(b.C*t^(-b.B)) :=
      mul_le_mul hi ((Real.exp_le_exp.mpr hs.2).trans hw) (exp_pos _|>.le) (by positivity)
    _ = b.C*t:= by rw [Real.rpow_add hg',Real.rpow_neg hg'.le,rpow_one]; field_simp
-- g(r) exact clock ratio across settings.
lemma gskin {s : I → ℝ} (h : b.Mid s) :
    Tendsto (fun i=> g (b.r i*exp (s i))/g (b.r i)) b.path (𝓝 1) := by
  let r:=b.r
  let x i:= G.slopeConstant*Real.log (r i)⁻¹; let y i:= G.slopeConstant*Real.log (r i*exp (s i))⁻¹
  have hd:=Gauge.slopeConstant_pos simple
  have hx : Tendsto x b.path atTop:=(log_kinetic simple).comp b.nearing
  have hy : Tendsto y b.path atTop:=(log_kinetic simple).comp (b.soon simple h)
  have hr : ∀ᶠ i in b.path, 0 < b.r i:= b.nearing.eventually self_mem_nhdsWithin
  have hX : ∀ᶠ i in b.path, 0 < x i:= hx.eventually_gt_atTop _
  have hpos : 0 < b.C := b.C0
  have hB : 0 < b.B := b.B0
  have he : Tendsto (fun i=> s i / x i) b.path (𝓝 0) := by
    -- height = log C + B/2 * log x
    have hh := ((show Tendsto (fun q : ℝ=>log q / (q^(1:ℝ))) atTop (𝓝 0) from (by simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero)).comp hx).const_mul (b.B/2)
    rw [mul_zero] at hh
    have hb := (hx.const_div_atTop (Real.log b.C)).add hh
    rw [zero_add] at hb; apply squeeze_zero' _ _ hb
    · exact (h.and hX).mono fun i ⟨hi,h⟩=> div_nonneg hi.1 h.le
    filter_upwards [h,hX] with i hi hp
    change _ ≤ _ + b.B/2*(log _ / x i^(1:ℝ)); rw [rpow_one]
    have ht : b.height i=log b.C+(b.B/2)*log (x i) := by
      change log (b.C*(√(x i))⁻¹^(-b.B))=_
      rw [log_mul,log_rpow,log_inv,Real.log_sqrt] <;> first | positivity | ring
    apply (div_le_div_of_nonneg_right hi.2 hp.le).trans_eq; rw [ht]; ring
  have hY:Tendsto (fun i=>y i/x i) b.path (𝓝 1) := by
    have hh := (tendsto_const_nhds (x:=(1:ℝ))).sub (he.const_mul G.slopeConstant)
    rw [mul_zero,sub_zero] at hh
    refine hh.congr' ?_
    filter_upwards [hX,hr] with i hp (hq:0<r i)

    rw [show y i=x i - G.slopeConstant*s i by unfold y x; rw [Real.log_inv, Real.log_mul hq.ne' (exp_pos _|>.ne'),Real.log_exp,Real.log_inv]; ring]; field_simp
  have hQ := (hY.sqrt).inv₀ (by norm_num); rw [Real.sqrt_one, inv_one] at hQ
  refine hQ.congr' ?_; filter_upwards [hX,hy.eventually_gt_atTop 0] with i hp hq
  change (√(y i / x i))⁻¹ = (√(y i))⁻¹ / (√(x i))⁻¹
  rw [sqrt_div hq.le]; ring_nf
lemma winding (s : I → ℝ) (h : b.Mid s) (t : ℝ→ℝ) (ht : Tendsto (fun r=> t r/g r) τ (𝓝 1)) :
    Tendsto (fun i=> t (b.r i*exp (s i)) / g (b.r i)) b.path (𝓝 1) := by
    have hh := (ht.comp (b.soon simple h)).mul (b.gskin simple h)
    rw [one_mul] at hh; apply hh.congr'
    filter_upwards [(b.soon simple h).eventually (positive_g simple), b.nearing.eventually (positive_g simple)] with i h h'
    dsimp; field_simp
end Loft

end
end YM.FVA2.GradedFar.Growth
