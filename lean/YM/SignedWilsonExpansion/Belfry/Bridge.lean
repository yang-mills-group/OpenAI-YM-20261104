import YM.SignedWilsonExpansion.Belfry.Pay
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SignedWilsonExpansion.Belfry
open Function Set Filter Asymptotics PowerSeries Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Menus MS.Book MS.Book.Program MS.Book.Convolve MS.Puff MS.Puff.Actors
open XSpace XSpace.Structure1 XSpace.Normalize FVA2 FVA2.Scale FVA2.Reg FVA2.Dframe
open WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK MarqueQ.Crops MarqueQ.Crops.Taught
open Dancer Commission Belle Belle.Path Belle.Buffet Future
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{ι σ κ κ':Type}{n q m d:ℕ}{L:Filter ι}{θ ε g:ι→ℝ}
namespace ScaleFits
section parameter
abbrev Yo (D:Guard G d)(t:ℝ)(b:ℕ): Sec G d→ₗ[ℂ] Sec G d:= young b t D
variable (h:Tendsto θ L (𝓝 0))
lemma bound_comp {E:Type}[SeminormedAddCommGroup E]{S:ℝ→E}(q:Continuous S) {v:ι→ℝ}(p:FO L v): FO L (S ∘ v):=by
    obtain ⟨C,h⟩:= isBigO_iff.mp p; let R:=Metric.closedBall (0:ℝ) C; obtain ⟨U,u⟩:= ((isCompact_closedBall ..).image q.norm).bddAbove; refine IsBigO.of_bound U (?_); filter_upwards [h] with i hi; refine (u (Set.mem_image_of_mem _ (show v i∈R from ?_))).trans_eq (by simp); rw [ Metric.mem_closedBall, dist_zero_right ]; simpa using hi
lemma budget_tracks {D:ℝ→Guard G d}(P:∀ i:ℕ, Meter.Tracks D i)(h:FO L θ) : Budget L (D ∘ θ):=by
    let V:=Module.finBasis ℂ (Sec G d)
    let f(x: Sec G d × Fin (Module.finrank ℂ (Sec G d))):= (V.coord x.2) ∘ₗ LinearMap.applyₗ x.1; have hP(x)(i:ℕ): Continuous (fun t=> f x (coeff i (D t))):=by
      obtain ⟨p,u⟩:= Rhythm.from_poly.mp (P i x.1 (V.coord x.2)); change Continuous (fun t=> V.coord x.2 ( coeff i (D t) x.1 )); rw [u]; exact p.continuous.comp Complex.continuous_ofReal
    obtain ⟨x,t,q⟩:= bought f (fun p h=> LinearMap.ext fun j=>V.equivFun.injective (funext fun i=> by rw [LinearMap.zero_apply,map_zero]; exact h (j,i))) -- exact names
    intro i u
    simp_rw [show ∀ j, u (coeff i ((D ∘ θ) j))=∑ k:x,u ( f k.val (coeff i ( D (θ j))) • t k ) from fun j=> (congr_arg u ( q _ )).trans (map_sum ..), _root_.map_smul]; apply IsBigO.sum; intro j t'; exact FO.mul (bound_comp (hP j.val i) h) (FO.const (u (t j)) _) -- map linear
lemma budget_clock {f:ℝ→ Cn}(t:Meter.Clear f)(h:FO L θ) : funds L (f ∘ θ):= by
    intro j; obtain ⟨q,h'⟩:= Rhythm.from_poly.mp (Rhythm.unit.mpr (t j)); have ht : Continuous (fun t=> coeff j (f t)):=by rw [h']; exact q.continuous.comp Complex.continuous_ofReal
    exact bound_comp ht h
lemma boundD (p:FO L θ)(d:ℕ): S' (L:=L) (fun i=> FVA2.Scale.Level.Dial d (G:=G) (θ i)):=by
    intro x; apply bound_comp (S:=fun t=> x ( Level.Dial d t )) _ p; unfold Level.Dial; simp_rw [map_sum,_root_.map_smul]; exact continuous_finsetSum _ (fun i _=> (by unfold Extent.token; fun_prop)) -- alias
lemma BoundConstant (S:Guard G d): Budget L (fun _=> S):= fun i t=> FO.const _ _
lemma convert_actual {M:ι→Guard G d}(h:Budget L M)(hp:FO L θ) : Budget L (fun i=> convertT (θ i) (M i)):=by
    have he: S' (L:=L) (fun i=> (Level.Dial d (G:=G)) ( -θ i )):= boundD (θ:=-θ) (hp.neg_left) _; intro b x; simp_rw [convertT,coeff_mk]; exact mulE ( mulE he (h b) ) (boundD hp d) x
variable {V:Normalize.Store G}(R:Initialize G)(K:Rose.Pick V){Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}(Q:Speed.Quoted R K Y S)(s:G.Simple)
variable (q0:FO L θ)
open GroupS
local notation "N"=> Measure.adjust R K d
include Q
lemma eaten (ν:ℝ)(p:FO L θ): funds L ( GroupS.ψ K Y ν ∘ θ ):= budget_clock ( Q.toContract.scales ν|>.check.smooth ) p
lemma checkedN (ν:ℝ)(p:FO L θ)(d:ℕ): Budget L (fun i=> gaugeN R K Y ν ( θ i ) d ):= budget_tracks ( Q.toContract.scales ν|>.check.proper d ) p
lemma permit (ν:ℝ)(t:ℝ): Tangent (GroupS.ψ K Y ν t):= Q.toContract.scales ν|>.check.led t
lemma editorial : Scale.Base N:= (Q.toContract.joint 0 d).2.2.scale
include s
lemma checked (ν:ℝ)(q:FO L θ)(d:ℕ): Budget L (fun i=> gaugeB K Y ν (θ i) d) :=by
    let U(t):= gaugeB K Y ν t d; let p:=GroupS.ψ K Y ν; let H:=editorial (d:=d) R K Q; let A:= FVA2.Scale.Measure.adjust R K d; obtain ⟨a,b,c⟩:= Q.toContract.toMission.born
    have he(μ:ℝ): gaugeB K Y ν μ d= convertT μ A* gaugeN R K Y ν μ d * Reg.Point.stepV ( p μ ) ( mirror A ):=by rw [Scale.Frame.step_mirror A H ( p μ ) ( permit R K Q ν μ ).start ( permit R K Q ν μ ).real, ← GroupS.relatingN ν R K Y S s a b c μ, mul_assoc, ( H.switch ( permit R K Q ν μ ).real ).turn', mul_one]
    simp_rw [he]; exact Budget.mul (Budget.mul ( convert_actual ( BoundConstant A ) q ) (checkedN R K Q ν q d)) (( BoundConstant _ ).until (eaten R K Q ν q) fun i=> (permit R K Q ν (θ i)).start )
omit Q s
abbrev Tick (q:Cn)(t:ℝ)(b:ℕ): ℝ:= ( calcT (t:ℂ) b q ).re
lemma pure_tick {q:Cn}(p:Tangent q)(t:ℝ)(b:ℕ): (Tick q t b:ℂ)= calcT (t:ℂ) b q:=by
   have hQ: (starRingEnd ℂ) ( calcT t b q )=calcT t b q:=by rw [timed,map_sum]; apply Finset.sum_congr rfl; intro i _; simp only [ _root_.map_mul,map_pow, show (starRingEnd ℂ) (coeff i q)=_ from Reg.Unique.coinR p.real i, Complex.conj_ofReal]
   obtain ⟨x,u⟩:= Complex.conj_eq_iff_real.mp hQ; unfold Tick; rw [u]; rfl
end parameter
end ScaleFits
end YM.SignedWilsonExpansion.Belfry
