import YM.Integration.WilsonOriginalPublicRelativeGramPins

/-! The common f-grid signed sales reach the physical relative frame without
substituting the fine-grid smeared Wilson form. Each mass is used once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramGrid
open Filter Finset Function Lattice Wilson RG Source Labels Cells OPE
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalBlissMixedGram (grades)
open WilsonOriginalPublicRelativeGramPins (physical matrix cutoff)
open WilsonOriginalPublicRelativeGramPosted (Dated issued gram submitted deposits printed)
open WilsonOriginalPublicPivotReflected (sampled evaluated board)
open WilsonOriginalPublicRelativeGramJoined (fee)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G)(W:Initialize G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {ℓ:Ultrafilter (ℕ×ℕ)}{I L:Type}[Fintype I][Fintype L]
  (a:Axis)(d:I→ℕ)(J:ℝ→PhysMS.tower S)(w:(i:I)→(Spin.comparator R.family.book).Field (d i))
  (r s:ℝ)(site:ℕ)(addresses:L→Fin 2→ Cover)(μ:L→ℂ)
  (Y:Bool→(ℕ×ℕ)→(i:I)→R.family.label (d i))
  (sale:Dated (L:=L) R W d)
local notation "C₀" => cutoff R a d site addresses μ Y
local notation "M" => matrix R F a d J w r s site addresses μ
local notation "T₀" => physical R a d site addresses Y
local notation "B" => sale.frame
local notation "A₀" => gram R W d sale
local notation "bank" => submitted R W d sale
local notation "old" => deposits R W d sale

def received (t:Bool)(z:ℕ×ℕ)(i j:I)(m:L):ℂ:=
  evaluated sale.q (sale.g z) (board R W (grades (d i) (d j)) (issued R W d sale t z i j) (sale.nodes z m) univ)

def charge (nodes:Bool→I→I→L→ℝ)(rest:Bool→I→I→ℝ)(t:Bool)(i j:I):ℝ:=
  (∑m,‖μ m‖*nodes t i j m)+rest t i j

omit [Fintype I] in
theorem weighted (t:Bool)(z:ℕ×ℕ)(i j:I)(mass:sale.mass z=μ)(cost:L→ℝ)
    (signed:∀m,μ m≠0 → ‖T₀ t z i j m-received R W d sale t z i j m‖ ≤ cost m):
    ‖C₀ t z i j-bank t z i j‖ ≤ ∑m,‖μ m‖*cost m:=by
  change ‖(∑m,μ m*T₀ t z i j m)-∑m,sale.mass z m*received R W d sale t z i j m‖ ≤ _
  rw [mass,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun m _=>?_
  by_cases empty:μ m=0
  · simp [empty]
  · rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (signed m empty) (norm_nonneg _)

variable [DecidableEq I]
theorem total (b:Bool→(i:I)→R.family.label (d i))(converges:∀t i,
    Tendsto (fun z=>Y t z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b t i)))
    (same:∀t i,S.project (d i) (b t i)=J (cond t s r) (d i) (w i))
    (below:(ℓ:Filter (ℕ×ℕ)) ≤ f.fuse)(admitted:∀m,μ m≠0→Extraction.Order.grid R.family site (addresses m)∈generic 2)
    (tuition rest:Bool→I→I→ℝ)(η:ℝ)(ep:0<η)
    (earned:∀ᶠ z:ℕ×ℕ in f.fuse,∀t i j,
      ‖C₀ t z i j-bank t z i j‖ ≤ tuition t i j ∧ old t z i j ≤ rest t i j)
    (rank:IsUnit (M false).det)(op:‖(M false)⁻¹‖*fee η (tuition false+rest false) ≤ 1/2):
    ∀ᶠ z:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)),IsUnit (B false z).det ∧
      ‖(M false)⁻¹*M true-(B false z)⁻¹*B true z‖ ≤
        2*‖(M false)⁻¹‖*(fee η (tuition true+rest true)+fee η (tuition false+rest false)*‖(M false)⁻¹*M true‖):=by
  have close:∀ᶠ z:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)),∀t i j,‖C₀ t z i j-M t i j‖ ≤ η:=by
    apply Filter.eventually_all.mpr; intro t
    apply Filter.eventually_all.mpr; intro i
    apply Filter.eventually_all.mpr; intro j
    have conv:=WilsonOriginalPublicRelativeGramPins.limit R F a d J w r s site addresses μ Y b
      converges same below admitted t i j
    exact ((Metric.tendsto_nhds.mp conv) η ep).mono fun z hz=>by simpa only [dist_eq_norm] using hz.le
  filter_upwards [close,earned.filter_mono below] with z cv ez
  have part(t:Bool)(i j:I):
      ‖C₀ t z i j-((B false z)ᴴ*A₀ z*B t z) i j‖ ≤ tuition t i j+rest t i j:=by
    calc
      _ ≤ ‖C₀ t z i j-bank t z i j‖+‖bank t z i j-((B false z)ᴴ*A₀ z*B t z) i j‖ := by
        simpa only [dist_eq_norm] using dist_triangle (C₀ t z i j) (bank t z i j) (((B false z)ᴴ*A₀ z*B t z) i j)
      _ ≤ _ := add_le_add (ez t i j).1 ((printed R W d sale t z i j).trans (ez t i j).2)
  have allFaces(t:Bool):‖M t-(B false z)ᴴ*A₀ z*B t z‖ ≤ fee η (tuition t+rest t):=by
    apply WilsonOriginalPublicRelativeGramPanel.entry_bound
    intro i j
    change ‖M t i j-((B false z)ᴴ*A₀ z*B t z) i j‖ ≤ η+(tuition t i j+rest t i j)
    calc
      _ ≤ ‖M t i j-C₀ t z i j‖+‖C₀ t z i j-((B false z)ᴴ*A₀ z*B t z) i j‖:=by
        simpa only [dist_eq_norm] using dist_triangle (M t i j) (C₀ t z i j) (((B false z)ᴴ*A₀ z*B t z) i j)
      _ ≤ _ := add_le_add ((norm_sub_rev _ _).le.trans (cv t i j)) (part t i j)
  exact WilsonOriginalPublicRelativeGramInverse.original _ _ _ _ _ rank _ _ (allFaces false) (allFaces true) op

theorem original (b:Bool→(i:I)→R.family.label (d i))(converges:∀t i,
    Tendsto (fun z=>Y t z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b t i)))
    (same:∀t i,S.project (d i) (b t i)=J (cond t s r) (d i) (w i))
    (below:(ℓ:Filter (ℕ×ℕ)) ≤ f.fuse)(admitted:∀m,μ m≠0→Extraction.Order.grid R.family site (addresses m)∈generic 2)
    (nodes:Bool→I→I→L→ℝ)(rest:Bool→I→I→ℝ)(η:ℝ)(ep:0<η)
    (earned:∀ᶠ z:ℕ×ℕ in f.fuse,sale.mass z=μ ∧ ∀t i j,
      (∀m,μ m≠0 → ‖T₀ t z i j m-received R W d sale t z i j m‖ ≤ nodes t i j m) ∧
      old t z i j ≤ rest t i j)
    (rank:IsUnit (M false).det)(op:‖(M false)⁻¹‖*fee η (charge μ nodes rest false) ≤ 1/2):
    ∀ᶠ z:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)),IsUnit (B false z).det ∧
      ‖(M false)⁻¹*M true-(B false z)⁻¹*B true z‖ ≤
        2*‖(M false)⁻¹‖*(fee η (charge μ nodes rest true)+fee η (charge μ nodes rest false)*‖(M false)⁻¹*M true‖):=by
  let tuition:=fun t i j=>∑m,‖μ m‖*nodes t i j m
  apply total R W F a d J w r s site addresses μ Y sale b converges same below admitted
    tuition rest η ep _ rank op
  filter_upwards [earned] with z ez
  exact fun t i j=>⟨weighted R W a d site addresses μ Y sale t z i j ez.1 _ (ez.2 t i j).1,(ez.2 t i j).2⟩

end YM.Integration.WilsonOriginalPublicRelativeGramGrid
