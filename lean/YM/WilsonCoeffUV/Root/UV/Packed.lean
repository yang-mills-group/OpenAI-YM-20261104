import YM.WilsonCoeffUV.Root.UV.Assembly
/-!
# Rent funds from projection graph. synchronized across comparisons. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V E:Type*}{r h D l j e k a N m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A B C x y δ σ γ H S O v:ℝ}
lemma glanceAway (F:Frame G h)(i: Alma F)(Y X:Single G D)(p:∀ i r, Standby (Y i r))(q:∀ i r,Standby (X i r)) (k):glean F (Y-X) k i=glean F Y k i-glean F X k i:=by
    unfold glean; dsimp only; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro r _; by_cases g:valence F i≤ k+r
    · simp only [if_pos g]; obtain ⟨s,A,b,u⟩:=p (k+r-valence F i) r; obtain ⟨t,B,a,v⟩:=q (k+r-valence F i) r; exact echo_minus F i u v b a
    simp [g]
lemma fundsN {I:Bulb G}(P Q:Island F D)(Y:Tand I e r D)(v:Alma F)(u:Y.Y=P.2 v)(w:Y.Z=Q.2 v)(p:Shimmer P)(q: Shimmer Q): Rent Y Y.Y F Y.x ∧ Rent Y Y.Z F Y.x ∧ Rent Y (Y.Y-Y.Z) F (Y.x*Y.σ):=by
    let a:=p.scan; let b:=q.scan; have ht (i j)(h:lowerGrade i j e r):= Y.rent i j h
    have h1:Y.Y=P.2 v:=u; have hq :=show Stakes Y.Y from u.symm ▸ affirm P.1 P.2 a v; have hg:=show Stakes Y.Z from w.symm ▸ affirm Q.1 Q.2 b v
    refine ⟨⟨hq,fun i j h=>(ht i j h).wax,fun i _=>(born_cost F v e Y.Y (u.symm ▸ epoch p v e) i).trans Y.P.rich⟩,⟨hg,fun i j h=>(ht i j h).wane,fun i _=>(born_cost F v e _ (w.symm ▸ epoch q v e) i).trans Y.P.rich⟩,hq.sub hg,fun i j h=>(ht i j h).toll,fun i _=>?_ ⟩
    rw [u,w, glanceAway F i _ _ (solo_stretch (a.solo v)) (solo_stretch (b.solo v)), epoch p v e i,epoch q v e i,sub_self,norm_zero]; exact mul_nonneg (zero_le_one.trans Y.P.rich) Y.P.θ

def legion {I:Cloister G h}(P:Stand (inkPin I))(Y: Thesis F D): Thesis F D:= fun i=> fanfare I.lamp.path P h (Y i)
-- stage rolling relation; else Strand.
structure Turbine (I:Cloister G h)(P:Stand (inkPin I))(Y Z:Island F D):Prop where
    walk: Shimmer Y
    paid i: Stakes (legion P Y.2 i)
    arrive: Shimmer Z
    licence : leaseM (inkPin I).patch.L F (lineS (prismata F (legion P Y.2)) 0)
    swept: impose Z.2 (prismata F (legion P Y.2))=legion P Y.2
lemma turbine_flow (A:Levels G)(Ñ:ChartRatio G)(u:m<N)(g:G.Simple)(H:Hol G)(p:LocalRatio Ñ)(v:Usage A Ñ m)(I:Cloister G h)(hx:inkPin I=v.gear)(R: Stand (inkPin I)) (e:HEq R (v.postStand u g p))(T:Courant I R)(Y:Island F D)(s:Shimmer Y)(k:h<D): Turbine I R Y (reglazed (descend A Ñ N m Y)):=by
    let F':= descend A Ñ N m Y; change Turbine I R Y (reglazed F'); have he : F'.2=legion R Y.2:= byPath A Ñ u g p Y v I hx R e
    obtain ⟨hv,hh⟩:=path_warp A Ñ k u g p H Y s I v hx R e T; have hq : Chain F F'.1 F'.2 := running A Ñ u g p s.scan
    refine ⟨s,fun i=>?_ ,hh,he ▸ hv,?_⟩
    · rw [← he]; exact affirm _ _ hq i
    rw [←he]; exact refluent (V:=F') (stellarized hv)

-- licencing pre constants. even if Tend only under Props.
def berth (_H:Hol G)(F:Frame G h)(_p:h<D)(u:ℝ)(j t:ℕ)(s:ℝ)(C:ℝ): Prop:=
    ∀ (I:Cloister G h)(P:Stand (inkPin I)) (Y Z: Island F D), Nonempty (Courant I P)→Turbine I P Y Z→ I.lamp.input=s → xota I=u → I.j=j → I.l=t →
    dragCup Bank.terrain I.lamp.s (inkPin I).D P.Q →(∀ k: Alma F,∃ A:ℝ,Twig 0 I.lamp.input A (Y.2 k 0 (valence F k))) → Rapt F (steed (lineS (prismata F (legion P Y.2)) 0) (inkPin I).patch.L) C
lemma licence (H:Hol G)(F:Frame G h)(p:h<D)(hx:0<x)(h₁:4≤j)(h₂:4≤l)(hv:h≤j)(t:0<s): ∃ C:ℝ,0≤C∧ berth H F p x j l s C:=by
    let F' := {v: Alma F × Alma F // valence F v.1=valence F v.2}
    choose C hC ht using fun v:F'=>quota H F v.val.1 v.val.2 v.property x hx j l h₁ h₂ hv p s t
    let Z:=∑ v,C v; have hZ :0≤ Z:= Finset.sum_nonneg fun _ _=> hC _
    obtain ⟨B,b,q⟩:= holdShelter F Z hZ; refine ⟨B,b,fun I P Y Z ⟨Q⟩ L hb hp hq he hZ HZ=>q (inkPin I).patch.L _ L.licence (fun i t h=>?_)⟩
    rw [coined]; let N:F':=⟨(i,t),h⟩; exact (ht N I P Q (Y.2 t) hb hp hq he (streams L.walk t) (L.paid t) ⟨_,hZ⟩ (HZ t)).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun x _ =>hC x) (Finset.mem_univ N)) (by positivity))

def ferryS (H:Hol G)(F:Frame G h)(p:h<D)(I:Cloister G h):ℝ:= (licence H F p (x:=xota I) (inkPin I).kernel.penalty_pos I.post I.inlet I.horizon I.lamp.inlet).choose
lemma ferryP (H:Hol G)(F:Frame G h)(p:h<D)(I:Cloister G h): 0≤ferryS H F p I ∧ berth H F p (xota I) I.j I.l I.lamp.input (ferryS H F p I):= (licence H F p (x:=xota I) (inkPin I).kernel.penalty_pos I.post I.inlet I.horizon I.lamp.inlet).choose_spec
def skulk (H:Hol G)(F:Frame G h)(p:h<D)(l r:ℕ)(I:Cloister G h):= shadesT F l*ferryS H F p I*velo H F p I.lamp r
lemma skulkP (H:Hol G)(F:Frame G h)(p:h<D)(l r:ℕ)(I:Cloister G h):0≤ skulk H F p l r I:=mul_nonneg (mul_nonneg (shadesT_nn F l) (ferryP H F p I).1) (velo_nn ..)

-- exact constants for station. e range. all earlier hypotheses intrinsic in Shimmer scans.
structure Hull (I:Cloister G h)(W:Rally (e+1) 0 (inkPin I))(P Q X Y:Island F D)(l k:ℕ)(A B D':ℝ):Prop where
    Pp:Turbine I W.P P X
    Qq:Turbine I W.Q Q Y
    vp:∀ v: Alma F,∃ x,Twig 0 I.lamp.input x (P.2 v 0 (valence F v))
    vq:∀ v: Alma F, ∃ x,Twig 0 I.lamp.input x (Q.2 v 0 (valence F v))
    U v i r: valence F v=l → lowerGrade i r e k → Shelf Bank.terrain 0 I.lamp.input W.x W.σ (P.2 v i r) (Q.2 v i r)
    D'' v i : i<e∨ i=e∧ valence F v<l → Shelf Bank.terrain 0 I.lamp.exitS W.x W.σ (X.2 v i k) (Y.2 v i k)
    V : Plinth P.2 Q.2 I.lamp.input e k l A B
    T v : valence F v=l → Twig 0 I.lamp.exitS D' (Y.2 v e k)
lemma PLover (H:Hol G)(F:Frame G h)(p:h<D)(e r l:ℕ)(h0:r≤l+e):∃ c:ℕ,∀ (I:Cloister G h),∃ C:ℝ,0≤ C∧∀ (W:Rally (e+1) 0 (inkPin I))(_G':Courant I W.P)(_T:Courant I W.Q)
    (Y V X Q:Island F D)(A B σ:ℝ), 0≤ A→1≤ σ→ I.lamp.dues r → Hull I W Y V X Q l r A B σ → Plinth X.2 Q.2 I.lamp.exitS e r l (skulk H F p l r I/(inkPin I).patch.L.val*A +C*W.x^c) (skulk H F p l r I/(inkPin I).patch.L.val *B+C*W.x^c*σ*(1+A)*W.σ):=by
   obtain ⟨d,hD⟩:= armada H F e r p; obtain ⟨k,h⟩:=summarize F r e D d
   refine ⟨d+(k+1),fun I=>?_⟩; obtain ⟨S,hS,v⟩:= hD I; obtain ⟨B,hB,hh⟩:= h I.lamp S hS; let Z:= ferryS H F p I; obtain ⟨C,hC,q⟩:= rise_graph (D:=D) F e r k l d h0 hB hS (ferryP H F p I).1
   refine ⟨C,hC,fun W G' T Y V X Q x A σ hx hs hb U=>?_⟩
   let P:= prismata F (legion W.P Y.2); let a':= prismata F (legion W.Q V.2)
   have hp:= W.Υ.mono (I.lamp.outlet.trans (inkPin I).holds.le); have hZ: Rapt F (steed (lineS P 0) (inkPin I).patch.L) Z:= (ferryP H F p I).2 I W.P Y X ⟨G'⟩ U.Pp rfl rfl rfl rfl hp.oneP U.vp
   have ht : Rapt F (steed (lineS a' 0) (inkPin I).patch.L) Z:= (ferryP H F p I).2 I W.Q V Q ⟨T⟩ U.Qq rfl rfl rfl rfl hp.otherP U.vq
   refine q (inkPin I).patch.L P a' X.2 Q.2 hx W.rich hs W.θ (fun i=> (streams U.Pp.arrive i).born) (fun i=> (streams U.Qq.arrive i).born) U.Pp.licence U.Qq.licence hZ ht ?_ U.T U.D''
   let p' i (h:valence F i=l): Tand I.lamp e r D := ⟨W,Y.2 i,V.2 i,fun k j h' => U.U i k j h h'⟩
   have hx' i (h:valence F i=l): Wager (p' i h) F x A (velo H F p I.lamp r) S d:= by
      obtain ⟨e,t,h'⟩:= fundsN Y V (p' i h) i rfl rfl U.Pp.walk U.Qq.walk; exact v _ G' T hb e t h' x A (U.V.pose i h) (U.V.vale i h) (U.V.peek i h)
   refine ⟨fun i h=>?_,fun i h=>?_,fun i h=>?_,⟨fun i j m n g=>?_⟩⟩
   · unfold P; rw [U.Pp.swept]; exact (hx' i h).pose
   · unfold a'; rw [U.Qq.swept]; exact (hx' i h).vale
   · unfold P a'; rw [U.Pp.swept,U.Qq.swept]; exact (hx' i h).visit
   unfold P a'; rw [coined,coined]; have hz:= hh (p' j n) _ _ _ hx (hx' j n)
   refine ⟨hz.pose m i g,hz.vale m i g,?_⟩; rw [← mul_assoc]; exact hz.toll m i g
end YM.WilsonCoeffUV.Cosmos
