import YM.SignedWilsonExpansion.Homes.HomingP

/-! Geometry at one or two election homes. Costs on comparable normalized inputs. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {n:ℕ} {d:Caps n} {ι:Type*} {L:Filter ι}

lemma gearedGoal (q : MaxwellSlots C d) {t:ℝ} (ht:t≠0) {x:Points n}(hx:x∈conf n) :
   WickGoal (d:=d) (fun i=> gear C.labels (d i) t (q i)) (t•x) = WickGoal q x:= by
  let F:=C.labels
  let T := freeTable F
  let M := T.classMoment T d
  suffices h : (M (t•x)).compLinearMap (fun i=>gear F (d i) t)=M x from congrArg (fun W => W q) h
  ext1 v
  let ℰ(i:Fin n):=recorded F (d i)
  rw [Multilabel.expansion (fun i : Fin n => (ℰ i).b), Multilabel.expansion (fun i : Fin n => (ℰ i).b) (M x)]
  refine Finset.sum_congr rfl fun i _ => congrArg (_ • ·) ?_
  let k : (j:Fin n)→_ := fun j => (ℰ j).b (i j)
  change T.useAt T (t•x) (fun j=>⟨d j,gear F (d j) t (k j)⟩)=T.useAt T x (fun j=>⟨d j,k j⟩)
  rw [writes_eval,writes_eval]; simp only [k,rare,map_smul]
  exact rising_moment hx (fun j=> (ℰ j).weighs (i j)) ht

-- only points necessary at this stage
lemma gearHome (d:ℕ){r:ι→ℝ} {t:ℝ} {v:ι→(Bel C.book).Field d} {x:(Bel C.book).Field d}(hr:Tendsto r L (𝓝 t)) (hv:Tendsto v L (𝓝 x)):
    Tendsto (fun i=> gear C.labels d (r i) (v i)) L (𝓝 (gear C.labels d t x)) := by
   refine Dash.arcing (Dash.fit_plane _ _ (fun y=>?_)) hv
   show Tendsto (fun i=> gear C.labels d (r i) y) L (𝓝 (gear C.labels d t y))
   have H: Continuous (fun t=> gear C.labels d t y):= by
      let Q:=Extra.FD.recorded C.labels d
      conv => arg 1; ext x; rw [← Q.b.sum_repr y,map_sum]
      simp_rw [map_smul,Pert.Scale.rare]
      fun_prop
   exact H.continuousAt.tendsto.comp hr

def pivotT {H:Type*} (L:Filter H)(r ρ:H→ℝ):Prop:= ∀ᶠ i in L,r i ≤ ρ i ∧ ρ i ≤ 2*r i
lemma compare_pivot {r ρ:ι→ℝ}(h:Tendsto r L trail)(hr:pivotT L r ρ): Tendsto ρ L trail ∧ ∀ᶠ i in L, r i/ρ i∈ Icc (2:ℝ)⁻¹ 1 ∧ 0<ρ i:= by
   have ht: Tendsto r L (𝓝 0) := h.mono_right nhdsWithin_le_nhds
   have hv: Tendsto (fun i=>(2:ℝ)*r i) L (𝓝 0):=by simpa using ht.const_mul 2
   have μ:=hr.and (show ∀ᶠ i in L, 0 < r i from h.eventually self_mem_nhdsWithin)
   refine ⟨ tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩,?_⟩
   · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ht hv (hr.mono fun _ hi=>hi.1) (hr.mono fun _ hi=>hi.2)
   · exact μ.mono fun _ hi=> hi.2.trans_le hi.1.1
   filter_upwards [μ] with i H
   have p:= H.2.trans_le H.1.1
   refine ⟨⟨(le_div_iff₀ p).2 (by norm_num; linarith [H.1.2]),(div_le_one p).2 H.1.1⟩,p⟩

section residents
lemma pivotW {F:Final C f S}{J:ℝ→tower S}(H':Leading F J) {H:(Bel C.book).Hierarchy}{r ρ:ι→ℝ} {D:ι→ℕ}{P:ι→Panel S} (h:Tendsto r L trail)(hr:pivotT L r ρ)(hd:Tendsto D L atTop) (hs: ∀ᶠ i in L, HouseT F.room.kernel H (ρ i) (D i) (P i))
    {x:ι→Points n}{y:Points n}(hy:y∈conf n)(X:Tendsto x L (𝓝 y))(d:Caps n){w:ι→MaxwellSlots C d}{v:MaxwellSlots C d} (hv:∀ j,Tendsto (fun i=>w i j) L (𝓝 (v j))):
   Tendsto (fun i=> Coast (P i) (r i) (d:=d) (fun j=> gear C.labels (d j) (r i/ρ i) (w i j)) (x i)) L (𝓝 (WickGoal v y)) := by
   obtain ⟨p,hP⟩:=compare_pivot h hr
   refine regularly fun U hu=>?_
   let b(i):= r i/ρ i
   obtain ⟨t,θ,T⟩:=appointment (U:=U) (v:=b) (hZ:=isCompact_Icc) ((hP.filter_mono hu).mono fun i hi=>hi.1)
   have hp: 0< t := lt_of_lt_of_le (by norm_num) θ.1
   rw [← gearedGoal v hp.ne' hy]
   apply Tendsto.congr' _ (pickT H' (p.mono_left hu) (hd.mono_left hu) (hs.filter_mono hu) (Work.A05.smul_conf hp hy) (T.smul (X.mono_left hu)) d (fun j=> gearHome _ T ((hv j).mono_left hu)))
   filter_upwards [hP.filter_mono hu] with i hi
   dsimp only [Coast,b]; rw [smul_smul,mul_div_cancel₀ _ hi.2.ne']
end residents
end YM.SignedWilsonExpansion.Homes
