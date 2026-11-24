import YM.Integration.WilsonMaxwellThermometerPublicUniform
import YM.Integration.WilsonMaxwellThermometerPublicGalop

/-! All seven ordinary finite public faces on the plate with its original
three rounded microscopic sites. The common bound precedes both regulators. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicPlacedIncome
open Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress RG RG17 PhysMS PhysMS.Frame
open Filter Function Metric Set Finset Lattice Extraction Wilson Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose
open XSpace.Cirrus XSpace.Photo PhysicalNext.Repeat.Legato
open WilsonMaxwellThermometerShiftedPanel
open WilsonSeparatedOriginalThermometerCells WilsonSeparatedOriginalThermometerDetectorMesh
open WilsonMaxwellThermometerPublicStation (aperture granted)
open WilsonMaxwellThermometerPublicGalop (quotient)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(s:ℝ→ℕ)

private theorem neighborhood (read:Sample 3→ℂ)(out:Points 3→ℂ)
    (h:Senses (conf 3) read out){ε:ℝ}(he:0<ε):
    ∀ᶠ m in Front,∀x∈tsupport (Rose.test K),∀v:pack 3,
      dist (Extraction.tag m.spacing v) x≤24*m.spacing →
      dist (read (translated m v)) (out x) ≤ ε:=by
  let X := tsupport (Rose.test K)
  have stored : IsCompact X := (Rose.test K).hasCompactSupport
  have valid : X ⊆ conf 3 := (Rose.test K).tsupport_subset
  choose radius positive fee using fun x : X => sensesU h x.val (valid x.property) (ε/2) (half_pos he)
  let ballX (x : X) := ball x.val (radius x/2)
  obtain ⟨u,cover⟩ := stored.elim_finite_subcover ballX (fun _=>isOpen_ball)
    (fun x hx=>mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (half_pos (positive _))⟩)
  have shrink (k : X) : ∀ᶠ m in Front,(24:ℝ)*m.spacing<radius k/2 := by
    have t := frontier.endpt.const_mul (24:ℝ)
    rw [mul_zero] at t
    exact t.eventually (gt_mem_nhds (half_pos (positive k)))
  filter_upwards [accepted,(eventually_all_finset u).mpr (fun k _=>(fee k).and (shrink k))] with m admit budget x hx v good
  obtain ⟨k,hxk⟩ := mem_iUnion.mp (cover hx)
  obtain ⟨mem,inside⟩ := mem_iUnion.mp hxk
  have hk := budget k mem
  have close : dist x k.val < radius k/2 := inside
  refine (dist_triangle _ (out k.val) _).trans ?_
  apply le_trans (add_le_add ?_ ?_) ((add_halves ε).le)
  · apply le_of_lt (hk.1 _ _ admit ?_)
    change dist (familiar (translated m v)) k.val < radius k
    rw [location]
    exact (dist_triangle _ x _).trans_lt (by linarith [good,close,hk.2])
  · rw [dist_comm]
    exact senses_price h k.val (radius k) (positive k) _ (fee k) x (valid hx) (close.trans (half_lt_self (positive k)))


def limit (p:Tags G 6 3)(e:Fin 2)(S:Finset (Fin 3))(x:Points 3):ℂ:=
  if e=0 then scene x 6 (missing p S) else checked1 W V 6 x (missing p S)

theorem funded (p:Tags G 6 3)(e:Fin 2)(S:Finset (Fin 3)):
    Senses (conf 3) (fun x=>quotient W (V:=V) x p e.val S) (limit W (V:=V) p e S):=by
  fin_cases e
  · change Senses _ _ (fun x=>(scene x 6) (missing p S))
    simpa only [WilsonMaxwellThermometerPublicGalop.quotient,←detail] using
      (scans0 W V 6 (missing p S))
  · change Senses _ _ (fun x=>(checked1 W V 6 x) (missing p S))
    simpa only [WilsonMaxwellThermometerPublicGalop.quotient,←detail] using
      (scans1 W V 6 (missing p S))

def atParent (r:ℝ)(N per:ℕ)(live:s r≤N)(x:Points 3):Sample 3:=
  let z:=(N,per)
  let m:=chart R (s r) per (aperture R s r) (granted R s r)
  translated m (Mesh.back m ((R.family.S.toDepth live per).parent ∘ positions (R:=R) r z x))

private theorem same (m:Mesh)(v w:pack 3)(equal:wrap m.p.side ∘ v=wrap m.p.side ∘ w)
    (p:Tags G 6 3)(e:ℕ)(S:Finset (Fin 3)):
    quotient W (V:=V) (translated m v) p e S=quotient W (V:=V) (translated m w) p e S:=by
  have address:chartV (translated m v)=chartV (translated m w):=by
    funext i
    have h:=congrFun equal i
    change wrap m.p.side (v i+shift m)=wrap m.p.side (w i+shift m)
    simpa only [map_add,Function.comp_apply] using congrArg (· +wrap m.p.side (shift m)) h
  simp only [WilsonMaxwellThermometerPublicGalop.quotient,←detail]
  unfold cooked live
  simp only [address]
  rfl

theorem original (small:Tendsto (aperture R s) trail (𝓝 0))
    (room:WilsonMaxwellThermometerPublicUniform.Spacious R s)(p:Tags G 6 3){ε:ℝ}(pos:0<ε):
    ∀ᶠ r in trail,∀N per (live:s r≤N),∀x∈tsupport (Rose.test K),∀e:Fin 2,∀S:Finset (Fin 3),
      dist (quotient W (V:=V) (atParent R s r N per live x) p e.val S)
        (limit W (V:=V) p e S x)≤ε:=by
  have all:∀ᶠ r in trail,∀e:Fin 2,∀S:Finset (Fin 3),∀per:ℕ,
      let m:=chart R (s r) per (aperture R s r) (granted R s r)
      ∀x∈tsupport (Rose.test K),∀v:pack 3,dist (Extraction.tag m.spacing v) x≤24*m.spacing →
      dist (quotient W (V:=V) (translated m v) p e.val S) (limit W (V:=V) p e S x)≤ε:=
    eventually_all.mpr fun e=>eventually_all.mpr fun S=>
      WilsonMaxwellThermometerPublicUniform.boards R s small room
        (neighborhood K _ _ (funded W p e S) pos)
  filter_upwards [self_mem_nhdsWithin (s:=Set.Ioi 0),all] with r hr cash
  intro N per live x hx e S
  obtain ⟨v,hs,good⟩:=WilsonMaxwellThermometerParentLift.parents R.family.S live per hr x
  let m:=chart R (s r) per (aperture R s r) (granted R s r)
  rw [atParent,same W m _ v (by refine Eq.trans ?_ hs.symm;funext i;exact wrap_lift _)]
  exact cash e S per x hx v (by simpa only [m,chart,aperture,if_pos (show 0<r from hr)] using good)

end YM.Integration.WilsonMaxwellThermometerPublicPlacedIncome
