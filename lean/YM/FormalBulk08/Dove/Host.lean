import YM.FormalBulk08.Dove.West

/-! Plateau constant narrowed at most once. Pair stage post with L
lower conditions numerical; NOTHING to be filled recursively to obtain it. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch Exterior RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{j t E m n:ℕ}{σ η C A D :ℝ}
-- α≥θ strong

def Mulct (L:Side):ℝ:= (Real.sqrt (L.val:ℝ))⁻¹
lemma adhere {L:Side}{C:ℝ} (h:C^2≤(L.val:ℝ)): C/(L.val:ℝ)≤ Mulct L := by
    apply (div_le_iff₀ (show 0<(L.val:ℝ) by positivity)).mpr
    unfold Mulct; let z:=Real.sqrt (L.val:ℝ); have hp:0<z:=by unfold z; positivity
    have hg:z*z=(L.val:ℝ):=Real.mul_self_sqrt (by positivity)
    change C≤z⁻¹*(L.val:ℝ); rw [←hg,←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]; nlinarith
lemma gauss_price {F:Flight j t}{B k:ℝ}(h:RepeatPrices k η B F)(he:m≤j-2): gauss (Flight.duo k F).A0 η B m:= by
    intro l hh; convert (h l (hh.trans he)).1 using 1; rw [div_eq_mul_inv, inv_pow]
lemma pledge_raise {F:Flight j t}{V:Lodge F.patch}{Q ω:ℝ}(h:Pledge G K F V σ η A Q ω C m)(he:C≤D):Pledge G K F V σ η A Q ω D m:= by
    refine ⟨fun T u p v B W hp hW=>?_⟩; obtain ⟨Z,z,x⟩:= h.shop T u p v B W hp hW; exact ⟨Z,z,x.trans (add_le_add_right (mul_le_mul_of_nonneg_right he hW.1) _)⟩

structure Solo (G:Gauge)(K:KernelChoices)(σ η A B:ℝ)(j t m:ℕ)(W:ℝ):Prop where
    intense : ∀ P:Patch, W≤ (P.L.val:ℝ) → η ≤ P.L.val * σ ∧ ∀ (T:Lodge P) (U:ℝ), 0≤U →∃ D:ℝ,0<D∧∀ (F:Flight j t) (V:Lodge F.patch), ∀ p:F.patch=P,p ▸ V=T→ (locating G K F V).strip η U→ (roots G K F V).strip η U→ RepeatPrices K.penalty η B F→ Pledge G K F V σ η A A (Mulct F.L) D m
lemma fill_solo (G:Gauge)(K:KernelChoices)(hj:5≤j)(he:0<η)(hp:0<σ)(hm:1≤m)(ha:0≤A)(hb:0≤C): ∃ W:ℝ,Solo G K σ η A C j t m W:=by
    obtain ⟨B,b,W⟩:= Aster.promises (n:=j) (u:=t) G K hp he ha ha hb hm
    let v:= osc σ m/2; have hV:0<v:=div_pos (osc_pos _ hp) (by norm_num); refine ⟨max (max (B^2) (η/σ)) (η*m/v),⟨fun P h=>?_⟩⟩; rw [max_le_iff,max_le_iff] at h -- nested
    obtain ⟨⟨hQ,hX⟩,h⟩:= h; have hx:η ≤ P.L.val* σ:= (div_le_iff₀ hp).mp hX; have ht:Threshold σ η m P.L:= (div_le_iff₀ hV).mp h
    refine ⟨hx,fun T U hU=>?_⟩; obtain ⟨D,d,V⟩:= W P T U hU; refine ⟨D,d,fun F Y hr hz hL hP q=>?_⟩; subst P; exact V F Y rfl hz ht hx hL hP (gauss_price q (by omega)) _ (adhere hQ)
lemma charge_raise {A:Levels G}{N M i}{F:Lodge (A.clock.op i 0).patch}{h:(A.clock.op i 0).patch.Branches K G}(hp:charge A N M i K η C F h)(he:σ≤η)(hd:C≤ D):charge A N M i K σ D F h:= by
   have ht:= mul_le_mul_of_nonneg_right hd (ratioR_pos A.S N (i+1) targetPower).le; exact ⟨strip_mono hp.single he hd,strip_mono hp.mean he hd,strip_mono hp.root he hd,strip_mono hp.line he ht,strip_mono hp.bend he ht,strip_mono hp.fix he ht⟩

structure Credentials (K:KernelChoices)(l:ℕ)(P:Patch)(F:Lodge P)(σ η A B:ℝ)(ρ:ChartRatio G)(E:ℕ):Prop where
    plus:0<B
    ship: η ≤ P.L.val*σ
    hail: ∀ e≤ E,∀ r≤ e+2,Bail (fame _) η (TO G P K e r) B
    cone: ∀ e≤ E,∀ r≤ e+2,Bail (fame _) η (WO P F ρ e r) B
    goods: ∀ (W:Levels G)(i N M:ℕ),i<N→ N≤M → W.clock.J i=l→ ∀ p:(W.clock.op i 0).patch=P, ∀ h:(W.clock.op i 0).patch.Branches K G,
            charge W N M i K η B (p.symm ▸ F) h
    parts: ∀ W:Levels G,∀ i N:ℕ,i<N → W.clock.J i=l →∀ p:(W.clock.op i 0).patch=P, (W.clock.op i 0).patch.Branches K G→ ∀ m,1≤m→ m+1 ≤ E+2 → Pledge G K (destination W N i) (show Lodge (W.clock.op i 0).patch from p.symm ▸ F) σ η A A (Mulct (W.S.block i)) B m
-- allocate every `Credentials` before recursive range, incl neighborhoods topology. Depends K fixed group independent amounts.
def Holidays (K:KernelChoices)(σ η A B:ℝ)(ρ:ChartRatio G)(j t E:ℕ):Prop:= ∀ P:Patch,P.J=j → B≤(P.L.val:ℝ) →∀ F:Lodge P,∃ C:ℝ,Credentials K t P F σ η A C ρ E
lemma holidays (K:KernelChoices)(G:Gauge)(hj:5≤j)(ht:4≤t):∃ u:ℝ,0<u∧∀ σ η A:ℝ, 0<σ→0<η→η≤u→0≤A→∀ (ρ:ChartRatio G)(E:ℕ),∃ W:ℝ,0<W∧Holidays K σ η A W ρ j t E:=by
    obtain ⟨σ,B,h,b,P,H⟩:= may_use G K j t (by omega) ht
    refine ⟨σ,h,fun σ' η A h' he hw ha ρ E=>?_⟩
    have hu (F:Flight j t): RepeatPrices K.penalty η B F:= fun l hl=> ⟨strip_mono (P F l hl).1 hw le_rfl,strip_mono (P F l hl).2 hw le_rfl⟩
    let S:=Finset.Icc 1 (E+1)
    obtain ⟨Z,z,R⟩:= uniform S (P:=fun m W=>Solo G K σ' η A B j t m W) (fun i hi=>fill_solo G K hj he h' (Finset.mem_Icc.mp hi).1 ha b.le) (fun i _ a H b h=> ⟨fun P p => H.intense P (h.trans p)⟩)
    refine ⟨Z,z,fun T q ht' F=>?_⟩
    obtain ⟨Y,y,Q⟩:= H T q F
    let X(m:ℕ)(C:ℝ):Prop:=∀ W:Levels G,∀ i N:ℕ,i<N→W.clock.J i=t→∀ p:(W.clock.op i 0).patch=T,(W.clock.op i 0).patch.Branches K G→Pledge G K (destination W N i) (show Lodge (W.clock.op i 0).patch from p.symm ▸ F) σ' η A A (Mulct (W.S.block i)) C m
    have ho i (ha:i∈S):∃ C,X i C:= by
       obtain ⟨D,d,V⟩:= ((R i ha).intense T ht').2 F Y y.le; refine ⟨D,fun W k N he hv p H'=>?_⟩; subst T
       have hQ:= charge_raise (Q W k N N he le_rfl hv rfl H') hw le_rfl; change W.clock.J (k+1)=j at q; subst t j; exact V (destination W N k) F rfl rfl hQ.mean hQ.root (hu (destination W N k))
    obtain ⟨D,d,V⟩:= uniform S ho (fun i _ a H b h => fun W k N he hv p H'=> pledge_raise (H W k N he hv p H') h)
    let U:= Finset.Icc 0 E ×ˢ Finset.Icc 0 (E+2)
    obtain ⟨C,c,HX⟩:= uniform U (P:=fun (i:ℕ×ℕ) C=>Bail (fame _) η (TO G T K i.1 i.2) C) (fun i _=> TO_bail G i.1 i.2 η T K) (fun _ _ C h D ht=> h.mono ht)
    obtain ⟨C',c',HY⟩:= uniform U (P:=fun (i:ℕ×ℕ) C=> Bail (fame _) η (WO T F ρ i.1 i.2) C) (fun i _=> WO_bail G i.1 i.2 η F ρ) (fun _ _ C h D ht=> h.mono ht)
    let W:=max (max Y D) (max C C'); refine ⟨W,lt_max_of_lt_left (lt_max_of_lt_left y),((R 1 (by simp [S])).intense T ht').1,fun e hi r hr=>?_,fun e hi r hr=>?_,fun T i N M hi hn hv p hh=> charge_raise (Q T i N M hi hn hv p hh) hw ((le_max_left ..).trans (le_max_left ..)),fun T i N hi ht p h m hm hx=> pledge_raise (V m (by simp [S,hm];omega) T i N hi ht p h) ((le_max_right ..).trans (le_max_left ..))⟩
    · exact (HX (e,r) (by simp [U,hi];omega)).mono ((le_max_left ..).trans (le_max_right ..))
    exact (HY (e,r) (by simp [U,hi];omega)).mono ((le_max_right ..).trans (le_max_right ..))
end YM.FormalBulk08.Dove
