
.mode column
.header on
.width 20

with
    old as (select * from results where version=:old_version),
    new as (select * from results where version=:new_version)
select
    old.benchmark,
    printf("%.3f", new.t_compile)                 as t_compile,
    printf("%.2f", new.t_compile / old.t_compile) as t_compile_rel,
    printf("%.3f", new.t_run )                    as t_run,
    printf("%.2f", new.t_run / old.t_run)         as t_run_rel
from
    old join new on old.benchmark = new.benchmark;
