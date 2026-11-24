import YM.PertExtension.VaneExtraction

/-! Errors in primary lifts and bounded coefficient extraction at a common
finite horizon. Still before compensating same-mark covariance. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1350000
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
variable {G : Gauge} {q : ℕ+} {n : ℕ} (d : ℕ)
local notation "reg" => (atTop : Filter ℕ)
variable {x : Points n} (hx:x∈conf n)(U:ℕ→Fin n→Cover)(hq:1<q.val)
abbrev PathReady (x:Points n)(q:ℕ+) (U:ℕ→Fin n→Cover):Prop:=∀ i j: Fin n, i≠j→ Adrift (x:=x) (q:=q) i j (fun t=> U t i) fun t=> U t j
variable (hu:PathReady x q U) {S:Type*}(f:S→Address G)
variable (i j:Fin n)(hi:i≠j)

abbrev pathSimple (G:Gauge)(q:ℕ+) (U : ℕ→Fin n→Cover) (t:ℕ) (i j:Fin n) : Bridge G := (if i=j then 0 else echo (side q t) (U t i) (U t j))
private lemma pathSymm t : ∀ i j c d, pathSimple G q U t i j c d=pathSimple G q U t j i d c:=by
  intro a b c e; unfold pathSimple; by_cases hz:a=b <;> first | rw [if_pos hz,if_pos hz.symm] | rw [if_neg hz,if_neg (Ne.symm hz)]
  rfl; apply echo_comm (side_even q t)
def lifted (t:ℕ) := primary d f (magnify q t) (pathSimple G q U t) (pathSymm (G:=G) (q:=q) U t)
include hq hu hx hi

lemma lift_low (a b:KeyIn G d): Tendsto (fun t:ℕ=>(lifted (q:=q) d U f t).cov (i,.inl a) (j,.inl b)) reg (𝓝 ((currentX hx G d).cov (i,a) (j,b))) := by
  let E t:= scopedValue (q:=q) d hx i j (fun t=>U t i) (fun t=>U t j) f t (.inl a) (.inl b)
  let c:=((currentX hx G d).cov (i,a) (j,b)).re
  have he:Tendsto E reg (𝓝 0):=low_fee d hx i j (fun t=>U t i) (fun t=>U t j) hq hi (hu i j hi) f a b
  have he' := he.add_const c
  let A i j := ((currentX hx G d).cov (i,a) (j,b)).re
  have hz' : Tendsto (fun t:ℕ=> (↑(E t+c):ℂ)) reg (𝓝 (↑(0+c):ℂ)):=Complex.ofRealCLM.continuous.continuousAt.tendsto.comp he'
  rw [zero_add,Prayer.integer] at hz'
  exact hz'.congr fun t=>by
    unfold E scopedValue currentError lifted primary pathSimple; dsimp only
    rw [map_sub,if_neg hi]
    have hr : 0<magnify q t:=pow_pos (by exact_mod_cast q.pos) _
    unfold Prayer.collect
    rw [exact_fee d f (magnify q t) _ _ _ hr] -- named placeholders
    simp [c]

variable [Finite S]
include hq hu hx
lemma path_price a b : ∃ C:ℝ,∀ᶠ k in reg, ‖scopedValue (q:=q) d hx i j (fun t=>U t i) (fun t=>U t j) f k a b‖≤C:= by
  letI:=Fintype.ofFinite S
  let M:=Finset.univ.sup (fun i=>street (f i).1)
  obtain ⟨b₀,hB,hCost⟩:=sense G d
  let D:=max b₀ (((M:ℕ):ℝ)^(d-1))
  obtain ⟨B,hp,hη⟩:= vane_extract (q:=q) d hx i j (fun t=>U t i) (fun t=>U t j) hq hi (hu i j hi) M -- h context name conflict
  exact ⟨B*D*D,(hη 1 zero_lt_one).mono fun k hk=>eastward f hk (one_le_pow₀ (Nat.one_le_cast.mpr hq.le)) hp.le (fun i=>Finset.le_sup (f:=fun i=>street (f i).1) (mem_univ _)) (le_max_right ..) (fun i=>(hCost i).trans (le_max_left ..)) _ _⟩
end YM.PertExtension.LatticePT
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
variable {G : Gauge} {q : ℕ+} {n : ℕ} (d : ℕ)
local notation "reg" => (atTop : Filter ℕ)
variable {x : Points n} (hx:x∈conf n)(U:ℕ→Fin n→Cover)(hq:1<q.val)
variable (hu:PathReady x q U) {S:Type*} [Finite S](f:S→Address G)
include hx hq hu
protected theorem lifted_bounded (a b:Fin n × (KeyIn G d ⊕ S)):∃ C≥(1:ℝ),∀ᶠ k in reg,‖(lifted (q:=q) d U f k).cov a b‖≤C:=by
    rcases a with ⟨i,p⟩;rcases b with ⟨j,t⟩; dsimp only [lifted,primary]
    let v:=fun i k=>U k i
    by_cases ht:i=j
    · exact ⟨1,le_rfl,by simp [pathSimple,ht]⟩
    obtain ⟨c,h⟩:=path_price d hx U hq hu f i j ht p t
    let T a b:ℝ:=((currentX hx G d).cov (i,a) (j,b)).re
    let D:=∑ a, ∑ b, T a b*((if p=.inl a then 1 else 0)*(if t=.inl b then 1 else 0))
    have hr k : 0<magnify q k:=pow_pos (by exact_mod_cast q.pos) _
    refine ⟨max 1 (c+‖D‖),le_max_left ..,?_⟩; refine h.mono fun k hk=> ?_
    let r:=magnify q k; let E:=mourn (passcode f r d p) (passcode f r d t);let Q:=pathSimple G q U k i j
    change ‖(↑(E Q):ℂ)‖≤_;rw [Complex.norm_real];unfold scopedValue at hk;rw [currentError,map_sub, Prayer.collect] at hk; change ‖E _ - E (arc _ _ T)‖≤c at hk
    have hp : E (arc d r T) = D:= exact_fee d f r T p t (hr k)
    rw [hp] at hk
    have hQ: Q=echo (side q k) (U k i) (U k j):= by unfold Q pathSimple;rw [if_neg ht]
    rw [hQ]
    exact (norm_le_insert _ D).trans ((add_le_add_left hk _).trans (le_max_right ..))
where
  norm_le_insert (x y:ℝ):‖x‖≤‖x-y‖+‖y‖:= le_trans (by rw [sub_add_cancel]) (norm_add_le ..)
end YM.PertExtension.LatticePT
