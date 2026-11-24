import YM.RG12.Arche.Unmarked
/-!
# Restore joint vector cost, including relative configuration neighborhoods
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}{l:Filter UVIndex}[l.NeBot] {M:∀ d, ℕ→RepChart C d}
  {d e n D k N p m:ℕ}
  {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "F!"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,MergeProof.Accent.generator G i≤ z) (x:ι)
set_option quotPrecheck false
local notation "a!"=> (P x).arc
variable {S : Table C.book} {f: Extraction.Order}
def cut {L : Register G}(S : Table L){d e:ℕ}(v:S.Field d)(w:S.Field e) : (i:Fin 2)→ S.Field (![d,e] i) := Fin.cases v (Fin.cases w fun i=>Fin.elim0 i)

-- Bilinear even at junk points, use exact classMoment
private lemma descale {L : Register G}(Z:Table L)(v:Z.Field d)(w:Z.Field e)(t:Points 2): Z.classMoment Z ![d,e] t (cut Z v w)= disc ![(⟨d,v⟩:Z.Tag),⟨e,w⟩] t:=by
   let z (i:Fin 2) := (⟨![d,e] i,cut Z v w i⟩:Z.Tag); have hh:![(⟨d,v⟩:Z.Tag),⟨e,w⟩]=z:=by funext i; fin_cases i<;>rfl
   rw [hh]; rfl

def paired {L:Register G}(K : Table L) (d e:ℕ) (t:Points 2) : K.Field d →ₗ[ℂ] (K.Field e →ₗ[ℂ] ℂ):=by
    let Z:= K.classMoment K ![d,e] t; let a(d e:ℕ) (i:Fin 2):=K.Field (![d,e] i)
    let U : K.Field d→K.Field e →ₗ[ℂ] ℂ := fun x=> Z.toLinearMap (cut K x 0) 1
    have H(x y): U x y=Z (cut K x y):=by unfold U; change Z (update (cut K x 0) (1:Fin 2) _) = _; exact congr_arg _ (funext fun i=>by fin_cases i<;> simp [update,cut]; rfl)
    exact {
      toFun:=U
      map_add' := fun x y=> LinearMap.ext (fun z=>by
          let W : K.Field d →ₗ[ℂ] ℂ:=Z.toLinearMap (cut K 0 z) 0
          have h(x): U x z=W x:=by rw [H]; exact congr_arg _ (funext fun i=>by fin_cases i<;> simp [update,cut]; rfl)
          rw [LinearMap.add_apply,h,h,h,map_add])
      map_smul' := fun c x =>LinearMap.ext (fun z=>by
          let W : K.Field d →ₗ[ℂ] ℂ:=Z.toLinearMap (cut K 0 z) 0
          have h(x): U x z=W x:=by rw [H]; exact congr_arg _ (funext fun i=>by fin_cases i<;> simp [update,cut]; rfl)
          change U (c • x) z=c* _; rw [h,h,map_smul]; rfl) }
lemma pair_at {L : Register G}(Z : Table L) (t:Points 2) (x:Z.Field d)(y:Z.Field e) : paired Z d e t x y = disc ![(⟨d,x⟩:Z.Tag),⟨e,y⟩] t := by
   change (Z.classMoment Z ![d,e] t).toLinearMap _ _ _ = _
   rw [MultilinearMap.toLinearMap_apply,← descale]; refine congr_arg _ (funext fun i=>?_); fin_cases i<;>simp [update,cut]; rfl

def spread {L:Register G}(K:Table L)(t:Points 2) {E X: Type} [AddCommGroup E][Module ℂ E][AddCommGroup X][Module ℂ X]
    {d e:ℕ}(P:E→ₗ[ℂ] K.Field d)(Q:X→ₗ[ℂ] K.Field e) : E →ₗ[ℂ] X→ₗ[ℂ]ℂ := ((paired K d e t).compl₂ Q).comp P
private lemma spreading {L:Register G}(K:Table L)(t:Points 2) {E X: Type} [AddCommGroup E][Module ℂ E][AddCommGroup X][Module ℂ X]
    {d e:ℕ}(P:E→ₗ[ℂ] K.Field d)(Q:X→ₗ[ℂ] K.Field e)(v w):
    spread K t P Q v w=disc ![(⟨d,P v⟩:K.Tag),⟨e,Q w⟩] t:=pair_at K t (P v) (Q w)

-- uniform by exact simplex expansion in the two price axes. Useful with moving pivot coordinates.
private def E (i : (C.labels.level d).Index) : C.label d:= Pi.single i 1
lemma mass_two {d e:ℕ}(p:C.label d→ₗ[ℂ] C.label e→ₗ[ℂ] ℂ) {K:ℝ}(hp:∀ i j, ‖p (E (C:=C) i) (E j)‖ ≤ K)(v w):
    ‖p v w‖ ≤ K * mass C d v * mass C e w:=by
  have hf{d:ℕ}(x:C.label d): x = ∑ i:(C.labels.level d).Index,x i • E (C:=C) i:=by
     ext i; rw [Finset.sum_apply]; symm; rw [sum_eq_single i (fun j _ h=> by simp [E,Ne.symm h]) (by simp)]; simp [E]
  conv_lhs=> rw [hf v,map_sum p, LinearMap.sum_apply,hf w]
  rw [mass,mass,Labels.Frame.coeffSize,Labels.Frame.coeffSize,Finset.mul_sum Finset.univ (fun i=> ‖v i‖),Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum; intro i _
  rw [mul_sum,map_smul,LinearMap.smul_apply,map_sum]
  apply le_trans (show ‖_‖ ≤ ‖v i‖ * ∑ j, ‖p (E i) (w j • E (C:=C) j)‖ from by rw [norm_smul]; gcongr; exact norm_sum_le ..)
  rw [mul_sum]; apply sum_le_sum; intro j _; rw [map_smul, norm_smul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hp i j) (norm_nonneg _)) (norm_nonneg _)).trans_eq
  ring

-- actually simultaneous *matrix* error. no costs per p. includes all pairs of horizons in the Poised datum.
include H h hp hZ
set_option maxHeartbeats 500000 in
lemma lamps (hP:f.PointLimits C S) (hF:(F!).Smooth) (hh:S.Symmetric)
    (hobs:Observing C H ϕ M)(hb: ϕ≤ f.fuse)
    {R:Set (Points 2)}(hR:IsCompact R)(hi:R⊆ conf 2)(hn:2≤n) :
    ∃ c:ℝ,0≤ c ∧ ∀ᶠ k in atTop,∀ T : ℕ→ℕ→TableL C D, Poised P B H O J n z k T→
      ∀ (Z:∀ i:Fin (D+1),Module.End ℂ (C.label i)), Comparer (ϕ:=ϕ) (hC:=H) l k D T (mag A a! k) Z→
        ∀ b:Fin 2→ Cover, let y:= tag (mag A a! k)⁻¹ b; y∈R → y∈generic 2→ ∀ (j i : Fin (D+1))(v : C.label j)(w:C.label i),
          ‖pair S (Order.grid C k b) (S.project j (aligned C M k (Z j) v)) (S.project i (aligned C M k (Z i) w))- freePair C y v w‖ ≤ c * Ship.budget A n k * mass C j v * mass C i w:=by
  choose c hc he using fun (j i:Fin (D+1)) (v:(C.labels.level j).Index) (w:(C.labels.level i).Index)=> at_lamps (l:=l) P B H h hp O J z hZ x hP hF hh hobs hb j i (E v) (E w) hR hi hn
  let u(i:Fin (D+1)) := (C.labels.level i).Index
  let c1(j i:Fin (D+1))(v:u j):= ∑ w:u i,c j i v w
  let c2(j i):=∑ v:u j,c1 j i v; let c3(j):=∑ i,c2 j i; let Q:=∑ j,c3 j
  have h1(j i v):0≤ c1 j i v:= Finset.sum_nonneg (fun w _=>hc ..)
  have h2(j i):0≤ c2 j i:=sum_nonneg fun v _=> h1 j i v
  have h3 j:0≤ c3 j:=sum_nonneg fun i _=> h2 j i
  have hX{ι : Type}[Fintype ι]{h:ι→ℝ}(H:∀ i,0≤h i)(j): h j ≤ ∑ i,h i:=single_le_sum (fun i _=>H i) (mem_univ j)
  refine ⟨Q,sum_nonneg (fun j _=>h3 _),?_⟩
  filter_upwards [eventually_all.mpr (fun j=> eventually_all.mpr (fun i=>eventually_all.mpr (fun v=>eventually_all.mpr (he j i v))))] with k hK T hT Z hB b y hy hY j i v w
  let D₁ j:= (S.project _).comp (aligned C M k (Z j)); let V:= Order.grid C k b; let g:∀ j:Fin (D+1), C.label j →ₗ[ℂ] (F!).Field j := fun j=> (F!).project j
  let p:= spread S V (D₁ j) (D₁ i) - spread (F!) y (g j) (g i)
  have hV(a:C.label j)(o:C.label i) : p a o=pair S V (D₁ j a) (D₁ i o) - freePair C y a o:=by
     unfold p; simp only [LinearMap.sub_apply]; rw [spreading,spreading];rfl
  change ‖pair S V (D₁ j v) (D₁ i w) - freePair C y v w‖ ≤ _
  rw [← hV]; apply mass_two
  intro a o
  rw [hV]
  exact (hK j i a o T hT Z hB b hy hY).trans (mul_le_mul_of_nonneg_right
    ((show c j i a o ≤ c1 j i a from hX (hc j i a) o).trans <| (show c1 j i a ≤ c2 j i from hX (h1 j i) a).trans ((show c2 j i ≤ c3 j from hX (h2 j) i).trans (show c3 j ≤ Q from hX h3 j))) (Ship.budget_pos ..).le)
end YM.RG12.Arche
