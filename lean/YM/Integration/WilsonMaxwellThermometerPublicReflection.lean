import YM.Integration.WilsonMaxwellThermometerPublicPlacedIncome
import YM.Integration.WilsonMaxwellThermometerOriginal

/-! The normalized reflected two-slot position regulator with the two
singleton means subtracted, including their first variations. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicReflection
open Filter Set Finset Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Normalize
open XSpace.Cirrus XSpace.Photo XSpace.Rose XSpace.Structure1 XSpace.AxesTangent
open XSpace.Tornado XSpace.Retirement WilsonMaxwellThermometerChiralSlots
open WilsonMaxwellThermometerChiralReading
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)(V:Normalize.Store G)

def energy (G:Gauge)(s:Bool):Sec G 4 :=
  ((Rose.f:ℂ)^2*(2:ℂ)⁻¹) • ⟨polar G s,Submodule.sum_mem _ fun _ _=>team_label _ _ le_rfl⟩

theorem minus (G:Gauge):energy G false=WilsonMaxwellThermometerOriginal.lower G:= by
  apply Subtype.ext
  change (((Rose.f:ℂ)^2*(2:ℂ)⁻¹) • polar G false)=((Rose.f:ℂ)^2) • XSpace.Chiral.U G
  rw [WilsonMaxwellThermometerOriginalChirality.original,smul_smul]

def pair (b:Sec G 6)(s:Bool)(θ:Signed):Tags G 6 2 :=
  ![b,up (by decide : 4≤6) (ori θ.ortho 4 (reel 4 (energy G s)))]

def face (p:Tags G 6 2)(x:Sample 2)(e:ℕ)(S:Finset (Fin 2)):ℂ :=
  ∑ f∈tally e 2, if ∀i:Fin 2,i∉S→f (some i)=0 then
    PowerSeries.coeff (f none) (numberA W 6 x (pulseU f (deck (V.layout W (grab x) 6)) p) S)
  else 0

def limit (p:Tags G 6 2)(e:Fin 2)(S:Finset (Fin 2))(x:Points 2):ℂ :=
  if e=0 then scene x 6 (missing p S) else checked1 W V 6 x (missing p S)

theorem issued (p:Tags G 6 2)(e:Fin 2)(S:Finset (Fin 2)):
    Senses (conf 2) (fun x=>face W V p x e.val S) (limit W V p e S):=by
  fin_cases e
  · change Senses _ _ (fun x=>scene x 6 (missing p S))
    simpa only [face,←detail] using scans0 W V 6 (missing p S)
  · change Senses _ _ (fun x=>checked1 W V 6 x (missing p S))
    simpa only [face,←detail] using scans1 W V 6 (missing p S)

def ground (v:Finset (Fin 2)→ℂ):ℂ:=v univ-v {0}*v {1}

def slope (v w:Finset (Fin 2)→ℂ):ℂ:=w univ-w {0}*v {1}-v {0}*w {1}

theorem centered (p:Tags G 6 2):
    Senses (conf 2) (fun x=>ground (face W V p x 0))
      (fun x=>ground (fun S=>limit W V p 0 S x)) ∧
    Senses (conf 2) (fun x=>slope (face W V p x 0) (face W V p x 1))
      (fun x=>slope (fun S=>limit W V p 0 S x) (fun S=>limit W V p 1 S x)):=by
  constructor
  · intro x hx
    exact ((issued W V p 0 univ) x hx).sub
      (((issued W V p 0 {0}) x hx).mul ((issued W V p 0 {1}) x hx))
  · intro x hx
    exact (((issued W V p 1 univ) x hx).sub
      (((issued W V p 1 {0}) x hx).mul ((issued W V p 0 {1}) x hx))).sub
        (((issued W V p 0 {0}) x hx).mul ((issued W V p 1 {1}) x hx))

private theorem bounded {A:Sample 2→ℂ}{f:Points 2→ℂ} {K:Set (Points 2)}
    (law:Senses (conf 2) A f)(compact:IsCompact K)(apart:K⊆conf 2):
    ∃C:ℝ,∀ᶠ m in Front,∀x:Sample 2,grab x=m→welcome x→familiar x∈K→‖A x‖≤C:=by
  obtain ⟨D,hD⟩ := (compact.image_of_continuousOn ((law.priced.mono apart).norm)).bddAbove
  refine ⟨1+D,?_⟩
  filter_upwards [law.placed compact apart 1 zero_lt_one] with m good x same here mem
  calc
    ‖A x‖ = dist (A x) 0 := (dist_zero_right _).symm
    _ ≤ dist (A x) (f (familiar x)) + dist (f (familiar x)) 0 := dist_triangle .. 
    _ ≤ 1+D := add_le_add (good x same here mem) (by
      rw [dist_zero_right]
      exact hD (Set.mem_image_of_mem _ mem))

/-- The same upper bound applies to both genuinely reflected chiral energies
on the compact separated auxiliary plate. Every proper face uses its own
normalized finite integral and the same position prescription. -/
theorem original (b:Sec G 6)(θ:Signed){K:Set (Points 2)}(compact:IsCompact K)(apart:K⊆conf 2):
    ∃C:ℝ,∀ᶠ m in Front,∀x:Sample 2,grab x=m→welcome x→familiar x∈K→∀s:Bool,
      ‖slope (face W V (pair b s θ) x 0) (face W V (pair b s θ) x 1)‖≤C:=by
  choose C law using fun s:Bool=>bounded (centered W V (pair b s θ)).2 compact apart
  refine ⟨max (C false) (C true),?_⟩
  filter_upwards [law false,law true] with m h₀ h₁ x same here hx s
  cases s
  · exact (h₀ x same here hx).trans (le_max_left ..)
  · exact (h₁ x same here hx).trans (le_max_right ..)

end YM.Integration.WilsonMaxwellThermometerPublicReflection
