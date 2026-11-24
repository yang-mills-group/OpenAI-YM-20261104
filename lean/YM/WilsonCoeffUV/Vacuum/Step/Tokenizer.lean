import YM.WilsonCoeffUV.Vacuum.Step.Sponsor
/-!
# Supplies. Choose in order: overlapping ν,c costs BEFORE any patch length,
then width needs in the window, then m-growth of L (inlet restrictions and
energy thresholds), then all patch-local post charges. None bounds a sewn
front yet; schedule closure downstream. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{k r:ℕ} {s A B C:ℝ}

lemma renovation {R U:FreeResolvent.FaceRow}(h:R.strip s A)(e:U.strip s A)(b:0≤ A)(he:(minusRows R U).strip s C)(hp:0≤C)(hs:0<s): dragCup terrain s (kinPrice s C) (plain G R-plain G U):=by
   let H:= plaster G (minusRows R U); let V:= plaster G R; let W:=plaster G U
   have hz : H= minusRows V W:= by
      have hh := plaster_fee (G:=G) h hs.le b; have h' := plaster_fee (G:=G) e hs.le b; have hp': H.strip s (kinPrice s C):= plaster_fee (G:=G) he hs.le hp
      apply bank_injective (Row.rights _ _ hp' hs.le) (Row.rights _ _ (strip_minus hh h') hs.le);
      intro n; rw [acts_minus hs.le hh h']; unfold H
      rw [plaster]; ext1 i j; rw [coloration_act,hBlock_periods hs.le he, Matrix.sub_apply,plaster,plaster]; rw [coloration_act,coloration_act,hBlock_periods hs.le h,hBlock_periods hs.le e, acts_minus hs.le h e]
      unfold Precision.K; rw [Matrix.mul_sub,Matrix.sub_mul]; split<;> simp
   have he': plain G R-plain G U=shuttleM H:=by rw [hz]; rfl
   rw [he']; exact plain_cost G he hs.le hp

section prep
variable (A:Levels G)(m:ℕ)

def rag (i:ℕ) := Real.sqrt (Extension.UV.Linear.Dcost A.clock.kernel.penalty (A.clock.J i)*(A.S.a i/A.S.a m))
structure Glint (A:Levels G)(m:ℕ)(s B sig D:ℝ): Prop where
    main (N:ℕ) (h:m<N): Crank (shuttleM (groove A N m)) 3 s B
    θ (N:ℕ) (h:m<N): dragCup terrain s D (shuttleM (wagon A N m))
    single (N:ℕ) (h:m ≤ N): dragCup terrain s sig (plain G (freeForms A N m))
    shift (i N N':ℕ) (ht:m+1≤ i)(h:i≤N)(g:i≤N'): Ballast s D (rag A (m+1) i) (shuttleM (feedA A N m)) (shuttleM (feedA A N' m)) ∧ Ballast s D (rag A (m+1) i) (shuttleM (conditional A N m)) (shuttleM (conditional A N' m))
    kite (i N N':ℕ)(hr:m≤ i)(he:i≤N)(hv:i≤N'): Ballast s D (rag A m i) (plain G (freeForms A N m)) (plain G (freeForms A N' m))

lemma Glint.shrinks {s t B Z D :ℝ}(h:Glint A m s B Z D)(ht:t≤s): Glint A m t B Z D := ⟨fun N v=>(h.main N v).mono le_rfl ht,fun N v=>(h.θ N v).mono ht,fun N v=>(h.single N v).mono ht,fun i N n p t u=>let V:=h.shift i N n p t u; ⟨V.1.mono ht,V.2.mono ht⟩, fun i N n p t u=> (h.kite i N n p t u).mono ht⟩

structure Tokenizer (K: KernelChoices)(G:Gauge)(i j:ℕ) where
   s:ℝ
   sigma:0<s
   preB:ℝ
   pre_nn :0≤preB
   sig : ℝ
   sig_nn:0≤sig
   bid (P:Patch):ℝ
   bid_pos P: 1≤ bid P
   port (A:Levels G) (m:ℕ): A.clock.kernel=K→ A.clock.J m=i→ A.clock.J (m+1)=j → Glint A m s preB sig (bid (loose A m))

theorem current_stamp (K:KernelChoices)(G:Gauge){i j:ℕ}(hp:4≤ i)(ht:5≤ j): Nonempty (Tokenizer K G i j):=by
  set k:=K.penalty; have hk:0<k:=K.penalty_pos
  obtain ⟨s,C,hs,hc,T⟩:= forms_tail k hk i hp
  obtain ⟨t,B,hT,hB,H⟩:= crank_fee G k hk (j:=j) (t:=i) (by omega) hp
  obtain ⟨v,hv,HH⟩:=schedule_flat K G j i (by omega) hp
  set σ:=min s (min t v); have hσ:= lt_min hs (lt_min hT hv); have hU :σ≤t := (min_le_right ..).trans (min_le_left ..); have hw:σ≤v:= (min_le_right ..).trans (min_le_right ..)
  set S:=kinPrice s C
  have h : ∀ P:Patch,∃ D:ℝ,1≤D ∧ ∀ A:Levels G,∀ m:ℕ,loose A m=P→ A.clock.kernel=K → A.clock.J m=i→ A.clock.J (m+1)=j→ Glint A m σ B S D := by
    intro P
    classical
    by_cases e:∃ (A:Levels G) (m:ℕ),loose A m=P ∧ A.clock.kernel=K ∧ A.clock.J m=i ∧ A.clock.J (m+1)=j
    · have he:P.Branches K G ∧ P.J=j:=by obtain ⟨A,m,he,hv,hx,hy⟩:=e; subst K P; exact ⟨(A.blocks m 0).branches,hy⟩
      obtain ⟨D,hD,G'⟩:= HH P he.2 he.1
      set Z:= max 1 (max S D); have hZ:= le_max_left 1 (max S D)
      have hy:S ≤ Z:=(le_max_left ..).trans (le_max_right ..); have hz:D ≤ Z:= (le_max_right ..).trans (le_max_right ..)
      refine ⟨Z,hZ,?_⟩; intro A m hp' ha hb ho
      have hx : A.clock.kernel.penalty = k:=congr_arg KernelChoices.penalty ha
      have hF:= T A m hb hx
      have hr:= G' A m hp' ha hb
      have hM (N:ℕ): dragCup terrain σ S (plain G (freeForms A N m)):= (plain_cost G (hF.1 N) hs.le hc.le).mono (min_le_left ..)
      refine ⟨fun N _=> (H A m N hx hb ho).mono (by omega) hU,fun N p=>((matrix_width (hr.actual N p).2.2 hD.le).mono hw).le hz,fun i _=>hM i,?_,?_⟩
      · intro b N N' p hn hn'
        let l:= rag A (m+1) b
        have hl:0≤l:=Real.sqrt_nonneg _
        have HD := hr.gap b p N N' hn hn'; have HE:=hr.actual N (p.trans hn); have HF:=hr.actual N' (p.trans hn')
        refine ⟨(show Ballast σ D l _ _ from ⟨(matrix_width HE.2.1 hD.le).mono hw, (matrix_width HF.2.1 hD.le).mono hw, (matrix_width HD.2 (mul_nonneg hD.le hl)).mono hw⟩).fee hl hz, (show Ballast σ D l _ _ from ⟨(matrix_width HE.1 hD.le).mono hw,(matrix_width HF.1 hD.le).mono hw,(matrix_width HD.1 (mul_nonneg hD.le hl)).mono hw⟩).fee hl hz⟩
      intro u N N' p hn hn'
      let l:=rag A m u; have hl:0≤l:=Real.sqrt_nonneg _
      refine (show Ballast σ S l _ _ from ?_).fee hl hy
      have hf: (minusRows (freeForms A N m) (freeForms A N' m)).strip s (C*l):= by unfold l rag; rw [hx]; exact hF.2 u p N N' hn hn'
      refine ⟨hM N,hM N',?_⟩
      have hc': S*l=kinPrice s (C*l):=by unfold S kinPrice; ring
      rw [hc']; exact (renovation (hF.1 N) (hF.1 N') hc.le hf (mul_nonneg hc.le hl) hs).mono (min_le_left ..)
    exact ⟨1,le_rfl,fun A m p h t z=> False.elim (e ⟨A,m,p,h,t,z⟩)⟩
  choose F hZ hF using h
  exact ⟨σ,hσ,B,hB.le,S,kinPrice_nn _ _ hc.le,F,hZ,fun A m t v w=>hF _ A m rfl t v w⟩
end prep
end YM.WilsonCoeffUV.Bank
