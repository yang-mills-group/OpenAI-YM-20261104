import YM.WilsonCoeffUV.Root.UV.Rate
/-!
# Limits in canonical marked spaces. Width and exit fee inherited, commits order harmony; not reading when sector inapplicable. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}{θ:ℕ→ℝ}
section
variable [NormedAddCommGroup U] {P Q:ℕ→ Ten U (Cloth α) r}{R L:Ten U (Cloth α) r}
def Fleets (θ:ℕ→ℝ)(s:ℝ)(P:ℕ→ Ten U (Cloth α) r)(Q:Ten U (Cloth α) r):Prop:= ∃ A,∀ᶠ n:ℕ in atTop, Shelf Bank.terrain 0 s A (θ n) (P n) Q
lemma Fleets.point (g:Fleets θ s P R)(h:Tendsto θ atTop (𝓝 0))(x): Tendsto (fun n=>P n x) atTop (𝓝 (R x)):=by
    obtain ⟨A,hp⟩:=g; rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun n=> norm_nonneg _) (hp.mono fun n u=>u.toll.2 x) ?_; simpa using (h.const_mul A).mul_const (Real.exp (-s*tread Bank.terrain 0 x))
lemma Fleets.add (g:Fleets θ s P R)(h:Fleets θ s Q L): Fleets θ s (P+Q) (R+L):=by obtain ⟨A,hg⟩:=g; obtain ⟨C,he⟩:= h; exact ⟨_,(hg.and he).mono fun n ⟨v,q⟩=>v.add q⟩
lemma Fleets.gulp {P:ℕ→ Ten U (Cloth (α⊕β)) r}{R:Ten U (Cloth (α⊕β)) r}(h:Fleets θ s P R): Fleets θ s (fun n=>scoop (P n)) (scoop R):=by obtain ⟨A,h⟩:=h; exact ⟨_,h.mono fun n v=>v.gulp⟩
lemma Fleets.zero :Fleets θ s (0:ℕ→ Ten U (Cloth α) r) 0:=⟨_, Eventually.of_forall fun _=> Shelf.zero⟩
lemma Fleets.fleetSum {P: V →ℕ →Ten U (Cloth α) r}{Q:V→Ten U (Cloth α) r}{S:Finset V}(h:∀ i∈ S,Fleets θ s (P i) (Q i)): Fleets θ s (fun n=>∑ i∈S,P i n) (∑ i∈S,Q i):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Fleets.zero
    | @insert i s p ih=> simp_rw [Finset.sum_insert p]; exact (h i (Finset.mem_insert_self ..)).add (ih fun i t=>h i (Finset.mem_insert_of_mem t))
lemma Fleets.μ [NormedSpace ℝ U](h:Fleets θ s P R)(c:ℝ): Fleets θ s (c•P) (c•R):=by obtain ⟨A,u⟩:=h; exact ⟨_,u.mono fun n v=> v.μ c⟩
variable [CompleteSpace U]
lemma sunburn (p:Tendsto θ atTop (𝓝 0))(h:∀ b≥ m, ∀ i j,b≤ i→ b≤ j → Shelf Bank.terrain 0 s A (θ b) (P i) (P j))(v:m≤b)(q:b≤N): Shelf Bank.terrain 0 s A (θ b) (P N) (oblige P):=by
   have ht :∀ x,Tendsto (fun n=>P n x) atTop (𝓝 (oblige P x)):= by
      intro x; let y:= Real.exp (-s*tread Bank.terrain 0 x); apply augC (δ:=fun b=> A*θ b*y) (by simpa using (p.const_mul A).mul_const y); exact (eventually_ge_atTop m).mono fun i u j n hj hn=> (h i u j n hj hn).toll.2 x
   have hv:= h b v N N q q; refine ⟨hv.wax,⟨hv.nn,fun x=> le_of_tendsto (ht x).norm ((eventually_ge_atTop b).mono fun n hn=> (h b v n n hn hn).wax.2 x)⟩,⟨hv.toll.1,fun x=> le_of_tendsto (tendsto_const_nhds.sub (ht x)).norm ?_⟩⟩
   exact (eventually_ge_atTop b).mono fun n hn=> (h b v N n q hn).toll.2 x
end
variable (L:Theatre H T p e E W)
def glory (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(m:ℕ): Thesis F D:= fun i k r=> oblige (fun n=> (Peaks A Ñ T p n m).2 i k r)
abbrev Theatre.matron (m:ℕ):= glory L.V.draws L.V.paid T p m
lemma cheers (P:Sees H T p e E W U' i k r)(h:L.V.anchor ≤m)(v:m≤ b)(q:b≤ N)(j: Alma F)(hj:valence F j=k) : Shelf Bank.terrain 0 (L.angle m h).lamp.exitS (L.V.cash U' m) (L.V.tempC m b) ((L.lore N m).2 j i r) (L.matron m j i r):= sunburn (P:=fun N=> (L.lore N m).2 j i r) (PathCost.fade L.V.draws.S m) (fun b hb i j' hi hq=> P L m h b i j' hb hi hq j hj) v q
lemma fleetOff (h:L.V.anchor≤m)(v:i≤e)(j:Alma F)(r): Fleets (L.V.tempC m) (L.angle m h).lamp.exitS (fun n=>(L.lore n m).2 j i r) (L.matron m j i r):= ⟨_,(eventually_ge_atTop m).mono fun _n hn=> cheers L ((allPlays H T p e E W).choose_spec i _ _ v) h hn le_rfl j rfl⟩
lemma gleaming (h:L.V.anchor≤ m)(v:i≤ e)(j:Alma F)(r x): Tendsto (fun N=> (L.lore N m).2 j i r x) atTop (𝓝 (L.matron m j i r x)):= (fleetOff L h v j r).point (PathCost.fade L.V.draws.S m) x
-- support lane at R.ω
lemma fleetOn (h:L.V.anchor≤m)(v:i≤ e)(j:Alma F)(r): Fleets (L.V.ωJ m) (L.angle m h).lamp.input (fun n=>(L.lore n (m+1)).2 j i r) (L.matron (m+1) j i r):=by
   obtain ⟨A,f⟩:=fleetOff L (m:=m+1) (by omega) v j r; refine ⟨A,f.mono fun n hn=>?_⟩; have hv:= hn.shrink (L.touch m h); exact ⟨hv.wax,hv.wane,hv.toll.cost (mul_le_mul_of_nonneg_left (L.V.also_temp h) hv.nn)⟩
end YM.WilsonCoeffUV.Cosmos
