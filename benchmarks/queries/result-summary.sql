
.mode column
.header on
.width 20

with
  averaged as
    (select
      run,
      run_timestamp,
      lang,
      backend,
      benchmark,
      avg(t_compile) as t_compile_avg,
      avg(t_run)     as t_run_avg
    from
      results natural join runs group by run, lang, backend, benchmark)
select * from averaged order by run, lang, benchmark, backend;
