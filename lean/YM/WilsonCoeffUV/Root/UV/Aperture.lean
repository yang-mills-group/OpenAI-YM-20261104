import YM.WilsonCoeffUV.Root.UV.InstallRoot
/-! # Aperture delay after L. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos.Polestar
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Supply Ticket
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}
lemma afLog (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(I:Cloister G h): ∀ᶠ z:ℝ in atTop,underway H F p e I → Repose H T p e I z∧ flagC H F p e I ≤ z:=by
    let E:=Finset.range (e+1); let V:= Finset.range (e+h+1); let S:= Finset.range (h+1)
    have hv (k r l:ℕ): ∀ᶠ z:ℝ in atTop,∀ v:r≤l+k,hills H F p k r l v I≤ z:= by by_cases h: r≤l+k; exact (eventually_ge_atTop (hills H F p k r l h I)).mono fun i hn v=>hn; exact Eventually.of_forall (fun z v=>False.elim (h v))
    have ht (k r:ℕ):∀ᶠ z:ℝ in atTop,∀ i: Alma F, umbra T p i k r I.lamp.exitS≤ z := eventually_all.mpr fun i=>eventually_ge_atTop _
    filter_upwards [(eventually_all_finset E).mpr (fun k _=> (eventually_all_finset V).mpr (fun r _=>(eventually_all_finset S).mpr (fun j _=>hv k r j))), (eventually_all_finset E).mpr (fun k _=> (eventually_all_finset V).mpr (fun r _=> ht k r)),eventually_ge_atTop I.lamp.exitS⁻¹,eventually_ge_atTop (flagC H F p e I)] with z i j x y
    exact fun Y=> ⟨⟨Y.1,Y.2,fun k r l t q v=> i _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega)) v,fun a k r t q=> j _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by have H:= valence_cap F a; omega)) a,x⟩,y⟩

-- equality lemma by extWant
lemma spike (Ñ:ChartRatio G)(K:A'.clock.kernel=A.clock.kernel)(L:A'.clock.J i=A.clock.J m)(H:A'.clock.J (i+1)=A.clock.J (m+1))(U:A'.clock.J (i+2)=A.clock.J (m+2)) (X:A'.S.block i=A.S.block m){p:5≤A.clock.J (m+1)}{p':5≤A'.clock.J (i+1)}(g:h+1≤A.clock.J (m+1)-2)(g':h+1≤ A'.clock.J (i+1)-2)(u:craftQuest A m e p)(u':craftQuest A' i e p')(v:roomV A m p)(v':roomV A' i p'): liftWing Ñ g u v=liftWing Ñ g' u' v':=by
   have hD : ∀ (K K':KernelChoices)(i j m n:ℕ)(p:4≤ i)(p':4≤ m)(u:5≤j)(u':5≤n), K=K' → i=m → j=n → splash G K i j p u =splash G K' m n p' u'∧ saffron G K i j p u=saffron G K' m n p' u'∧ knotV G K i j p u=knotV G K' m n p' u':=by intro K K' i j m n t t' g g' he hp hv; subst i j K'; exact ⟨rfl,rfl,rfl⟩
   have hb:= hD _ _ _ _ _ _ (A.clock.adm _) (A'.clock.adm _) p p' K.symm L.symm H.symm
   have hF:= hD _ _ _ _ _ _ (A.clock.adm _) (A'.clock.adm _) (upstairs A _ p) (upstairs A' _ p') K.symm H.symm U.symm
   have he:regionV Ñ u v=regionV Ñ u' v':= by unfold regionV; congr 1; exact twinning K L H U X p p' u u'; exact hF.1; exact hb.2.1; exact hb.1; exact hb.2.2
   unfold liftWing; congr 1; exacts [H.symm,L.symm]

lemma locks (Ñ:ChartRatio G) (K:KernelChoices) (L:Side)(H:Hol G)(T:SectionData F)(p:h<D)(j e e':ℕ): ∀ᶠ z :ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → A.S.block m=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2) (u:craftQuest A m e' v)(x:roomV A m v), underway H F p e (liftWing Ñ w u x) → Repose H T p e (liftWing Ñ w u x) z ∧ flagC H F p e (liftWing Ñ w u x) ≤ z:=by
    have hh a b: ∀ᶠ z:ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → A.clock.J m=a → A.clock.J (m+2)=b → A.S.block m=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤A.clock.J (m+1)-2)(u:craftQuest A m e' v)(x:roomV A m v),underway H F p e (liftWing Ñ w u x) → Repose H T p e (liftWing Ñ w u x) z ∧ flagC H F p e (liftWing Ñ w u x)≤ z:=by
       by_cases he:∃ (A:Levels G)(m:ℕ), A.clock.kernel=K ∧ A.clock.J (m+1)=j ∧ A.clock.J m=a∧ A.clock.J (m+2)=b∧ A.S.block m=L ∧∃ v:5≤A.clock.J (m+1), (h+1≤A.clock.J (m+1)-2) ∧ craftQuest A m e' v ∧ roomV A m v
       · obtain ⟨A,m,hp,hh,ha,hb,x,v,t,u,V⟩:= he; subst K a j b L
         filter_upwards [afLog H T p e (liftWing Ñ t u V)] with y hy; intro B i g h L x b w z s k; rw [←spike Ñ g L h x b t z u s V k]; exact hy
       exact Eventually.of_forall (fun c B i g h L x b w z s k W=>False.elim (he ⟨B,i,g,h,L,x,b,w,z,s,k⟩))
    let S:= Finset.range (j+2)
    filter_upwards [(eventually_all_finset S).mpr (fun a _=> (eventually_all_finset S).mpr fun b _=>hh a b)] with y h; intro A m p q l v w u x; have he:A.clock.J m≤ A.clock.J (m+1):= A.fits.mono m.le_succ; have hx:A.clock.J (m+2)≤A.clock.J (m+1)+1:= A.fits.stepSlow (m+1); exact h _ (show A.clock.J m∈ S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m p q rfl rfl l v w u x
end YM.WilsonCoeffUV.Cosmos.Polestar
