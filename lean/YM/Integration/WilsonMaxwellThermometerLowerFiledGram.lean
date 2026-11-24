import YM.Integration.WilsonMaxwellThermometerLowerPointGram

/-! The pointed numerical rows of the independent position programme
converge to the strictly detecting, centered Maxwell energy panel. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerLowerFiledGram
open Filter Set Finset Lattice Wilson Maxwell Maxwell.Free Table.Pairing
open XSpace XSpace.Normalize XSpace.Cirrus XSpace.Rose XSpace.Structure1
open WilsonMaxwellThermometerPublicReflection
open WilsonMaxwellThermometerLowerPointGram
open scoped Topology BigOperators Classical
variable {G:Gauge}(a:Axis)(x:E4)

def center:Points 2:=closedUp a (points fun _:Fin 1=>x) (points fun _:Fin 1=>x)

theorem separated (hx:0<x a):center a x∈conf 2:=by
  apply Table.Pairing.spans <;> exact ⟨fun _ _ _=>Subsingleton.elim _ _,fun _=>hx⟩

def field (z:occupied G a x):Sec G 4 :=
  ⟨z.val,(Submodule.span_le.mpr (fun w hw=>by
      obtain ⟨s,rfl⟩:=hw
      exact Submodule.sub_mem _ (energy G s).property
        (Submodule.smul_mem _ _ (leaf G 4).property)) : occupied G a x ≤ shellSector G 4) z.property⟩

private def raised (p q:Sec G 4):Tags G 6 2 :=
  Fin.append (fun _:Fin 1=>up (by decide : 4≤6) (ori (Signed.reflect a) 4 (reel 4 p)))
    (fun _:Fin 1=>up (by decide : 4≤6) q)

private theorem printed (p q:Sec G 4):
    scene (center a x) 6 (raised a p q)=score a x p.val q.val:=by
  rw [screen]
  apply congrArg (Maxwell.Wick.moment G (center a x))
  funext i
  fin_cases i <;> rfl

private theorem unit (s:Ortho): reflectPol s (realForm (1:WickPol G))=1:=by
  simp [realForm]

private theorem faces (p q:Sec G 4):
    ground (fun S=>scene (center a x) 6 (missing (raised a p q) S)) =
      score a x p.val q.val-score a x p.val 1*score a x 1 q.val:=by
  have h:(missing (raised a p q) univ)=raised a p q:=by funext i; simp [missing]
  have h₀:missing (raised a p q) {0}=raised a p (leaf G 4):=by
    funext i
    fin_cases i <;> rfl
  have h₁:missing (raised a p q) {1}=raised a (leaf G 4) q:=by
    funext i
    fin_cases i
    · apply Subtype.ext
      change (1:WickPol G)=reflectPol _ (realForm 1)
      exact (unit _).symm
    · rfl
  rw [ground,h,h₀,h₁,printed,printed,printed]
  rfl

def sample (W:Initialize G)(V:Normalize.Store G)(s:Bool)(z:occupied G a x)(t:Sample 2):ℂ:=
  ground (face W V (raised a (energy G s) (field a x z)) t 0)

theorem original (W:Initialize G)(V:Normalize.Store G)(hx:0<x a)(s:Bool)(z:occupied G a x):
    Tendsto (sample a x W V s z) (Gate (center a x)) (𝓝 ((panel G a x z) s)):=by
  rw [reported]
  change Tendsto _ _ (𝓝 (score a x (energy G s).val (field a x z).val-
    score a x (energy G s).val 1*score a x 1 (field a x z).val))
  rw [←faces a x (energy G s) (field a x z)]
  exact (WilsonMaxwellThermometerPublicReflection.centered W V _).1 _ (separated a x hx)

end YM.Integration.WilsonMaxwellThermometerLowerFiledGram
