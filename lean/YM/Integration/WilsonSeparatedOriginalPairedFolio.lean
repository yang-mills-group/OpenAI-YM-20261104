import YM.RG05Readout.Pulse.Chills

/-! Each genuine product test in the original finite smooth-source expansion carries the same signed center function into its own filed Wilson program. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalPairedFolio
open Function Filter Finset Set MeasureTheory Lattice RG RG05Readout RG05Readout.Native RG05Readout.Nuclear RG05Readout.Pulse
open RG05Readout.Flatten
open scoped BigOperators Topology ContDiff Classical
variable {X:Type*}{s:Fin 3→ℕ}{allow:(Fin 3→Body)→Prop}{book:(Fin 3→Body)→(X→ℂ)→Prop}

structure Entry (s:Fin 3→ℕ)(allow:(Fin 3→Body)→Prop)(book:(Fin 3→Body)→(X→ℂ)→Prop) where
  test:Fin 3→Body
  license:allow test
  size:∀i,Tall (test i) (s i+2) 1 1
  alpha:E4→ℂ
  rent:ℝ
  pos:0≤rent
  smooth:ContinuousOn alpha Native.box
  cap:∀z∈Native.box,‖alpha z‖≤rent
  value:X→ℂ
  filed:book test value

def submitted (L:List (Entry s allow book))(z:E4):Wave (Fin 3):=
  (L.map (fun e=>e.alpha z • joint univ e.test)).sum

theorem issued {F:E4→Wave (Fin 3)}{D:ℝ}(h:Bouquet s Native.box allow F D)
    (receipt:∀f,allow f→∃A,book f A):
    ∃L:List (Entry s allow book),(L.map Entry.rent).sum≤D ∧ EqOn (submitted L) F Native.box:=by
  induction h with
  | empty=>exact ⟨[],le_rfl,fun _ _=>rfl⟩
  | bloom f a t ha hx ht hf hc=>
    obtain ⟨A,registered⟩:=receipt f hc
    refine ⟨[⟨f,hc,hf,a,t,ht,ha,hx,A,registered⟩],?_,?_⟩
    · simp
    · intro z _;simp [submitted]
  | add _ _ hu hv=>
    obtain ⟨a,ha,ea⟩:=hu;obtain ⟨b,hb,eb⟩:=hv
    refine ⟨a++b,?_,?_⟩
    · simpa only [List.map_append,List.sum_append] using add_le_add ha hb
    · intro z hz;simpa only [submitted,List.map_append,List.sum_append,Pi.add_apply] using congr_arg₂ (·+·) (ea hz) (eb hz)
  | permit _ hx hp ih=>
    obtain ⟨a,ha,e⟩:=ih;exact ⟨a,ha.trans hp,e.trans hx⟩

def ink (g:Body)(e:Entry s allow book):ℂ:=∫z in Native.box,g.val z*e.alpha z

def mass (g:Body):ℝ:=∫z in Native.box,‖g.val z‖

theorem positive (g:Body):0 ≤ mass g:=integral_nonneg (fun _=>norm_nonneg _)

private theorem smooth (g:Body):Continuous g.val:=by
  have h:ContDiff ℝ ∞ g.val:=g.2;exact h.continuous

theorem cost (g:Body)(e:Entry s allow book):‖ink g e‖ ≤ mass g*e.rent:=by
  let μ:=volume.restrict Native.box
  have hi:Integrable (fun z=>‖g.val z*e.alpha z‖) μ:=
    ((smooth g).continuousOn.mul e.smooth).norm.integrableOn_compact Pert.Cellular.cells_compact
  have he:Integrable (fun z=>‖g.val z‖*e.rent) μ:=
    ((smooth g).norm.continuousOn.mul continuousOn_const).integrableOn_compact Pert.Cellular.cells_compact
  calc
    _ ≤ (∫z,‖g.val z*e.alpha z‖ ∂μ):=norm_integral_le_integral_norm _
    _ ≤ ∫z,‖g.val z‖*e.rent ∂μ:=by
      apply integral_mono_ae hi he
      filter_upwards [ae_restrict_mem Pert.Cellular.cells_compact.measurableSet] with z hz
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (e.cap z hz) (norm_nonneg _)
    _ = mass g*e.rent:=integral_mul_const ..

def received (g:Body)(L:List (Entry s allow book))(W:X):ℂ:=(L.map (fun e=>ink g e*e.value W)).sum

def exposed (g:Body)(L:List (Entry s allow book))(K:Wave (Fin 3)→ₗ[ℂ] ℂ):ℂ:=
  (L.map (fun e=>ink g e*K (joint univ e.test))).sum

private theorem sum_smooth (L:List (Entry s allow book))(K:Wave (Fin 3)→ₗ[ℂ] ℂ):
    ContinuousOn (fun z=>K (submitted L z)) Native.box:=by
  induction L with
  | nil=>simpa only [submitted,List.map_nil,List.sum_nil,map_zero] using (continuousOn_const:ContinuousOn (fun _:E4=>(0:ℂ)) Native.box)
  | cons e L ih=>
    have eq (z:E4):K (submitted (e::L) z)=e.alpha z*K (joint univ e.test)+K (submitted L z):=by simp [submitted]
    simp_rw [eq];exact (e.smooth.mul continuousOn_const).add ih

theorem measured (g:Body)(L:List (Entry s allow book))(K:Wave (Fin 3)→ₗ[ℂ] ℂ):
    (∫z in Native.box,g.val z*K (submitted L z))=exposed g L K:=by
  induction L with
  | nil=>simp [submitted,exposed]
  | cons e L ih=>
    have eq (z:E4):g.val z*K (submitted (e::L) z)=g.val z*e.alpha z*K (joint univ e.test)+g.val z*K (submitted L z):=by
      simp [submitted,mul_add,mul_assoc]
    have one:IntegrableOn (fun z=>g.val z*e.alpha z*K (joint univ e.test)) Native.box:=
      (((smooth g).continuousOn.mul e.smooth).mul continuousOn_const).integrableOn_compact Pert.Cellular.cells_compact
    have rest:IntegrableOn (fun z=>g.val z*K (submitted L z)) Native.box:=
      ((smooth g).continuousOn.mul (sum_smooth L K)).integrableOn_compact Pert.Cellular.cells_compact
    simp_rw [eq];rw [integral_add one rest,integral_mul_const,ih];rfl

theorem spent (g:Body)(L:List (Entry s allow book))(W:X)(K:Wave (Fin 3)→ₗ[ℂ] ℂ){ε:ℝ}
    (price:∀e∈L,‖K (joint univ e.test)-e.value W‖≤ε):
    ‖exposed g L K-received g L W‖ ≤ mass g*(L.map Entry.rent).sum*ε:=by
  induction L with
  | nil=>simp [exposed,received]
  | cons e L ih=>
    have tail:=ih (fun a ha=>price a (List.mem_cons_of_mem _ ha))
    have column:‖ink g e*(K (joint univ e.test)-e.value W)‖ ≤ mass g*e.rent*ε:=by
      rw [norm_mul];exact mul_le_mul (cost g e) (price e (List.mem_cons_self ..)) (norm_nonneg _) (mul_nonneg (positive g) e.pos)
    have eq:exposed g (e::L) K-received g (e::L) W=ink g e*(K (joint univ e.test)-e.value W)+(exposed g L K-received g L W):=by
      simp only [exposed,received,List.map_cons,List.sum_cons];ring
    rw [eq];exact (norm_add_le ..).trans ((add_le_add column tail).trans_eq (by simp only [List.map_cons,List.sum_cons];ring))

end YM.Integration.WilsonSeparatedOriginalPairedFolio
