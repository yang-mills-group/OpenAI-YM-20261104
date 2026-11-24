import YM.Integration.WilsonRunFormalMarkedStep

/-! A genuine positive-width rooted two-leg kernel pays the finite
position moment, including its entire tail. The limit is the prescribed
cover kinetic contraction, with the physical squared coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoverKineticMoment
open Function Finset Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Mesa Gorge City Cork Rift Pose Glide Bank Dawn Rial Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology

private def sites : Jolt Cover Site where
  give := fun n x => wrap n x
  undo := fun _ => lift
  back _ x := wrap_lift x
  tame x := (boil_drip (x, () )).mono fun _ h => congrArg Prod.fst h

private theorem point (η C A D : ℝ) (hC : 0≤C) (hA : 0≤A)
    (k : ℕ) (t b q : ℝ) (h : Real.exp (η*t)*‖b‖≤C)
    (p : ‖q‖≤A*(1+t)^k) (bound : (1+t)^k≤D*Real.exp (η/2*t)) :
    ‖b*q‖≤(C*A*D)*Real.exp (-(η/2)*t) := by
  have small : ‖b‖ ≤ C*Real.exp (-(η*t)) := by
    rw [Real.exp_neg,← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm (Real.exp _) _] using h)
  have pay : ‖q‖≤ A*(D*Real.exp (η/2*t)) := p.trans (mul_le_mul_of_nonneg_left bound hA)
  rw [norm_mul]
  calc
    _ ≤ (C*Real.exp (-(η*t)))*(A*(D*Real.exp (η/2*t))) :=
      mul_le_mul small pay (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = (C*A*D)*(Real.exp (-(η*t))*Real.exp (η/2*t)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem pair_limit {I : Type} (i j : I) (φ : Cover→ℝ) (T : Tile (Biglot I) 2)
    (S : (n : Side) → Tile (Tor n I) 2) (light : Light T S) (v : Cover) :
    Tendsto (fun n:Side=>S n ![(wrap n v,i),((0:Site n),j)] * φ (lift (wrap n v))) atTop
      (𝓝 (T ![(v,i),(0,j)]*φ v)) := by
  have raw := light (![(v,i),((0:Cover),j)])
  have node (n : Side) : drip n ∘ (![(v,i),((0:Cover),j)] : chain (Biglot I) 2)
      = ![(wrap n v,i),((0:Site n),j)] := by
    funext x; fin_cases x <;> simp [Lotus.drip]
  simp_rw [node] at raw
  refine (raw.mul (tendsto_const_nhds (x:=φ v))).congr' ?_
  filter_upwards [sites.tame v] with n hn
  rw [show lift (wrap n v)=v from hn]

private theorem pair_bound {I : Type} {n : Side} (x : Site n) (i j : I) (k : ℕ) (φ : Cover→ℝ)
    (A : ℝ) (hφ : Paddle k φ A) (S : Tile (Tor n I) 2) (η C D : ℝ)
    (hη : 0<η) (hn : Bail (lake n I) η S C)
    (paid : ∀ t≥(0:ℝ), (1+t)^k≤D*Real.exp (η/2*t)) :
    ‖S ![(x,i),(0,j)]*φ (lift x)‖ ≤ C*A*D*Real.exp (-(η/2)*(size (lift x):ℝ)) := by
  let w : chain (Tor n I) 2 := ![(x,i),(0,j)]
  have hw : skit n x ≤ wide (lake n I) w := by
    have m := skit_anchor n w (1:Fin 2) (0:Fin 2)
    simpa [w,skit,Laurent.size] using m
  have reached := palmed hn w (1:Fin 2)
  have rwgt : Real.exp (η*(size (lift x):ℝ))*‖S w‖≤C := by
    apply le_trans _ reached
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hw) hη.le
  exact point η C A D hn.1 hφ.1 k (size (lift x))
    (S w) (φ (lift x)) rwgt (hφ.2 _) (paid _ (Nat.cast_nonneg _))

private theorem decay {s:ℝ} (hs:0<s) :
    Summable (fun v : Cover => Real.exp (-s*(size v : ℝ))) := by
  have inj : Injective (fun v : Cover => (v,())) := fun _ _ h => congrArg Prod.fst h
  have cost := (coast_sum (I:=Unit) hs).comp_injective inj
  exact cost

theorem anchored {I : Type} (k : ℕ) (φ : Cover→ℝ) (A : ℝ) (hφ : Paddle k φ A)
    (i j : I) (T : Tile (Biglot I) 2) (S : (n : Side) → Tile (Tor n I) 2)
    {η : ℝ} (hη : 0<η) (purchased : Kith η T S) :
    Tendsto (fun n : Side => ∑ x : Site n, S n ![(x,i),(0,j)] * φ (lift x))
      atTop (𝓝 (∑' v : Cover, T ![(v,i),(0,j)] * φ v)) := by
  obtain ⟨C, HC⟩ := purchased.2
  have hC : 0≤C := HC.exists.choose_spec.1
  obtain ⟨D,hD,paid⟩ := Cork.pockets k (half_pos hη)
  let U := fun v : Cover => (C*A*D)*Real.exp (-(η/2)*(size v : ℝ))
  have sU : Summable U := (decay (half_pos hη)).mul_left (C*A*D)
  let pair := fun (n : Side) (x : Site n) => S n ![(x,i),(0,j)] * φ (lift x)
  have pos : ∀ v,0≤U v := fun v=>mul_nonneg (mul_nonneg (mul_nonneg hC hφ.1) hD.le) (Real.exp_pos _).le
  have priced : ∀ᶠ n in atTop, ∀x,‖pair n x‖≤U (sites.undo n x) :=
    HC.mono fun n hn x=>pair_bound x i j k φ A hφ (S n) η C D hη hn paid
  have conv := jolt_limit sites pair (fun v=>T ![(v,i),(0,j)]*φ v) U sU pos
    (pair_limit i j φ T S purchased.1) priced
  simpa only [pair,tsum_fintype] using conv

variable {G : Gauge} (R : Run G) (roofs : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
    (a : hue G)

theorem original (simple : G.Simple) (N i : ℕ) (hi : i<N) (e : ℕ)
    (tags : (n : Side) → (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices) :
    let V := R.family.path.levels
    let P := destination V N i
    let b := fun k=>(V.blocks k 0).branches
    let W := Dove.model V roofs b R.metals.O a N (i+1)
    let outgoing := fun n => Bank.burn P (roofs i) W R.metals.O (b i) tags n
    Tendsto (fun n : Side => ∑ x : Site n,
      (rancho (outgoing n) e 2 ![(x,coord (1:Axis),a),(0,coord (1:Axis),a)]) *
        (Cork.ch 0 (lift x)*Cork.ch 0 (lift x))) atTop
      (𝓝 (PowerSeries.coeff e (Roof.epoch a P (roofs i) V.clock.kernel W R.metals.O (b i)))) := by
  intro V P b W outgoing
  have bought := (Dove.genu V roofs b R.metals.O a R.alloy.B.ratio simple (i:=i+1) (N:=N) hi).toStory
  obtain ⟨η,hη,cost⟩ := Bank.componentwise P (roofs i) W R.metals.O (b i) bought (V.clock.adm i)
    R.alloy.B.ratio tags e 2 (0:Fin 2)
  obtain ⟨k,A,packet⟩ := (Cork.Pad.ch (0:Axis)).mul (Cork.Pad.ch (0:Axis))
  rw [Roof.epoch,Wine.scalar,PowerSeries.coeff_mk]
  exact anchored k _ A packet (coord (1:Axis),a) (coord (1:Axis),a) _ _ hη cost

end YM.Integration.WilsonCoverKineticMoment
end
