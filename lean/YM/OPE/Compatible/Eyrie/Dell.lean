import YM.OPE.Compatible.Eyrie.Peak
/-! # Budget on actual families -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Eyrie
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid
open PathData SectorNext.Vacuum Extra.Histories MergeProof MergeProof.Accent Owl
open scoped Topology Classical BigOperators
variable {G:Gauge}{d N k p:ℕ}{C:Family G}(h:C.Makes)
local notation "A"=>C.path.levels
local notation "Q"=>C.path.rep
local notation "F!"=>C.labels.level d
local notation "Rκ"=>Real.sqrt (C.path.levels.clock.forcedAllowance k)
local notation "l"=>C.ref d
local notation "r"=> (C.path.levels.params k)
variable {n:Side}
noncomputable def rhoE (R: Rep G n):ℝ:= R.v*Fintype.card (Site n)
variable (H:History G)(k':ℕ)(hq:H.Selected)
include hq
lemma flatE (p k:ℕ): ∃ a:ℝ, 0 ≤ a∧∀ N, k ≤ N→∀ U, ‖(H.rep N p k).exponent U-rhoE (H.rep N p k)‖ ≤ a:=by
         let k' := H.levels.params k; let b:= H.levels.clock.hatBeta k; let P:= H.levels.clock.loopCap k; obtain ⟨V,hV⟩:= labor (G:=G) (n:=H.S.side k p) (C:=k'.clip) (σ:=k'.width) (c:=k'.paths) (v:=P) (H.levels.budget k) (2*b); let z:= V+ Fintype.card (Site (H.S.side k p))*H.levels.clock.allowance k; refine ⟨max 0 z, le_max_left ..,fun N h U=>?_⟩; apply le_trans _ (le_max_right ..); let X:= H.rep N p k; have hv:= hq.represents N p k h; have hp: X.path.Bounds k'.clip k'.width k'.paths P:= hv.clip ▸ hv.good.paths
         have hc:X.beta∈ Set.Icc (b/2) (2*b):= hv.band; have he:1<b:= H.levels.fits.delayed k; have hx:‖X.beta‖ ≤ 2*b:=by rw[Real.norm_of_nonneg (le_trans (by linarith only [he]:0 ≤ b/2) hc.1)]; exact hc.2
         change ‖_‖≤ z; rw[Rep.exponent,rhoE,show (H.rep N p k).v * (Fintype.card (Site (H.S.side k p)) :ℝ)=(rhoE X) from rfl, show rhoE X - X.path.inChannels X.clip X.p X.beta U - X.activities.additive X.p U-rhoE X=-(X.path.inChannels X.clip X.p X.beta U) - X.activities.additive X.p U from by ring]; apply (norm_sub_le ..).trans; rw[norm_neg]; exact add_le_add (hv.clip.symm ▸ hv.vac.symm ▸ hV _ hp _ hx U) (Blinds hv.good.labels.boundE _)
omit hq
noncomputable abbrev shoulder (k:ℕ)(R:History G):ℝ:= Real.sqrt (R.levels.clock.forcedAllowance k)
noncomputable def nik (k d p:ℕ)(X:Family G)(b:ℝ): Prop:=∀ N, k≤N→∀ V: Coefficient (X.labels.level d) (X.side k p),∀ a:ℝ,V.remBound 0 (X.path.rep N p k) (shoulder k X.path) a→∀ U, ‖V.density 0 (X.localSection d) (X.path.rep N p k) U‖ ≤ Real.exp (rhoE (X.path.rep N p k))*b*(a+(X.labels.level d).coeffSize V.x)
include h
lemma nik_enroll (hk:C.ref d≤ k)(p:ℕ):∃ b:ℝ,0 ≤ b∧nik k d p C b:=by
        obtain ⟨a,h0,hV⟩:= flatE _ h.wilson p k -- A ?
        let Q':= (r).columns
        have hc:=(r).columns_ge; have hQ':1 ≤ Q':=hc; refine ⟨Real.exp a*(2+Q'),mul_nonneg (Real.exp_nonneg _) (by linarith only [hQ']),fun N hi V t ht U=>?_⟩
        let L:= C.path.rep N p k
        have h:= hV N hi U; let i:= L.exponent U; let z:=rhoE L
        have he: i-z ≤ a:= le_trans (Real.le_norm_self _) h
        have hz:Real.exp i ≤ Real.exp z*Real.exp a:=by rw [← Real.exp_add]; apply Real.exp_monotone; linarith only [he]
        have hw': C.path.levels.clock.forcedAllowance k ≤ 1:=by unfold Calendar.forcedAllowance; rw[Real.exp_le_one_iff]; apply neg_nonpos.mpr; exact Real.rpow_nonneg (Real.exp_nonneg _) _
        have hw:= Real.sqrt_le_sqrt hw'; rw[Real.sqrt_one] at hw
        have hp:= ‹C.Makes›.wilson.represents N p k hi
        let v:=(C.labels.level d).coeffSize V.x
        have hφ :‖V.exponentialEntry 0 (C.localSection d) L U‖ ≤ (1+Q')*v +t:= hull _ _ 0 _ _ (fun j=> by rw[show L.p=(A).budget k from hp.vac]; exact ‹C.Makes›.priced d k p hk 0 j) ht hw (zero_le_one.trans hc)
        refine (Penn U hp.good _ hw' ht hw hφ).trans (le_trans (mul_le_mul_of_nonneg_right hz (add_nonneg ((norm_nonneg _).trans hφ) (rem_nonneg ht))) ?_)
        have hx:(1+Q')*v+t+t ≤ (2+Q')*(t+v):=by
             have hh:= rem_nonneg ht; have he:0 ≤ v:= Work.G08.size_nonneg ..; nlinarith only [hh,he,hQ']
        exact (mul_le_mul_of_nonneg_left hx (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))).trans_eq (by unfold v; ring)
omit h
end YM.OPE.Eyrie
